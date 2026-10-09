import XCSP3Bridges as XB
import QUBOConstraints as QC
import MathOptInterface as MOI

# Preserve raw order/duplicates for serializer qualification; the standard
# Utilities.Model canonicalizes functions before returning them.
struct RawPayloadFixtureModel
    inner::MOI.Utilities.Model{Float64}
    raw::MOI.ScalarAffineFunction{Float64}
end
MOI.get(model::RawPayloadFixtureModel,attribute,args...)=MOI.get(model.inner,attribute,args...)
MOI.get(model::RawPayloadFixtureModel,::MOI.ConstraintFunction,
    ::MOI.ConstraintIndex{MOI.ScalarAffineFunction{Float64},MOI.EqualTo{Float64}})=
    MOI.ScalarAffineFunction(copy(model.raw.terms),model.raw.constant)

"Serialize an unordered raw row against its original exact polynomial."
function milp_raw_payload_case(parameters)
    count=get(parameters,"terms",16)
    count>=0 || throw(ArgumentError("nonnegative raw fixture size required"))
    linear=MOI.Utilities.Model{Float64}()
    variables=MOI.add_variables(linear,3)
    terms=[MOI.ScalarAffineTerm(Float64(mod(i,7)-3),variables[mod(i,3)+1]) for i in 1:count]
    append!(terms,[MOI.ScalarAffineTerm(2.0^53,variables[2]),
        MOI.ScalarAffineTerm(1.0,variables[2]),MOI.ScalarAffineTerm(-2.0^53,variables[2])])
    raw=MOI.ScalarAffineFunction(copy(terms),-7.0)
    MOI.add_constraint(linear,MOI.ScalarAffineFunction(copy(terms),-7.0),MOI.EqualTo(11.0))
    model=RawPayloadFixtureModel(linear,raw)
    state=(;linear=model,sources=[1,2],root=3,domain_relations=0,operation_relations=0)
    prepare=()->state
    operation=state->XB.bridge_payload(state)
    verify=(state,payload)->begin
        row=only(payload["equalities"])
        row["constant"]=="-7" && row["rhs"]=="11" || return false
        indices=[term["variable"] for term in row["terms"]]
        issorted(indices) && allunique(indices) || return false
        all(term->!iszero(parse(BigInt,term["coefficient"])),row["terms"]) || return false
        for a in -2:2,b in -2:2,c in -2:2
            values=(a,b,c)
            original=BigInt(-7)+sum(BigInt(term.coefficient)*values[term.variable.value] for term in raw.terms;init=big(0))
            emitted=parse(BigInt,row["constant"])+sum(parse(BigInt,term["coefficient"])*values[term["variable"]]
                for term in row["terms"];init=big(0))
            original==emitted || return false
        end
        raw.terms==terms && raw.constant==-7.0
    end
    (;prepare,operation,verify)
end

"Exhaustive original-domain witnesses derived from the emitted primitive equations."
function primitive_equality_oracle(payload, width)
    binary = Set(payload["binary_variables"])
    equations = [(terms=Dict(t["variable"] => parse(BigInt, t["coefficient"])
            for t in e["terms"]), constant=parse(BigInt, e["constant"]),
            rhs=parse(BigInt, e["rhs"])) for e in payload["equalities"]]
    groups = [collect(keys(e.terms)) for e in equations
        if !isempty(e.terms) && all(k -> k in binary, keys(e.terms)) &&
            all(==(1), values(e.terms)) && e.constant == 0 && e.rhs == 1]
    sort(length.(groups)) == [width, width, width^2] || return false
    length(Set(Iterators.flatten(groups))) == length(binary) || return false
    # Infer each selector's original wire values from the equations themselves;
    # Set iteration order and bridge variable numbering are never assumed.
    rows = []
    for group in groups
        coupled = []
        for e in equations
            wires = [k for k in keys(e.terms) if !(k in binary)]
            selectors = [k for k in keys(e.terms) if k in binary]
            length(wires) == 1 && !isempty(selectors) && all(k -> k in group, selectors) || continue
            push!(coupled, (wire=only(wires), equation=e))
        end
        isempty(coupled) && return false
        push!(rows, [Dict(c.wire => (c.equation.rhs - c.equation.constant -
            get(c.equation.terms, selector, big(0))) // c.equation.terms[c.wire]
            for c in coupled) for selector in group])
    end
    sources, root = payload["source_variables"], payload["root_variable"]
    local_index = findfirst(g -> length(g) == width^2, groups)
    local_index === nothing && return false
    local_rows = rows[local_index]
    expected_rows = Set((a, b, Int(a == b)) for a in 0:width-1 for b in 0:width-1)
    Set((r[sources[1]], r[sources[2]], r[root]) for r in local_rows) == expected_rows || return false
    for a in 0:width-1, b in 0:width-1
        values = zeros(BigInt, payload["variables"])
        values[sources] = [a, b]; values[root] = Int(a == b)
        for (group, group_rows) in zip(groups, rows)
            matches = findall(r -> all(values[k] == v for (k, v) in r), group_rows)
            length(matches) == 1 || return false
            values[group[only(matches)]] = 1
        end
        satisfied = all(e.constant + sum(c * values[k] for (k, c) in e.terms) == e.rhs
            for e in equations)
        satisfied == (a == b) || return false
    end
    true
end

"Serialize a prepared bridge while independently checking its primitive equations."
function milp_payload_case(parameters)
    width = get(parameters, "width", 8)
    construction = milp_construction_case(parameters)
    program = construction.prepare()
    bridge = construction.operation(program)
    prepare = () -> bridge
    operation = state -> XB.bridge_payload(state)
    verify = (state, payload) -> primitive_equality_oracle(payload, width)
    (; prepare, operation, verify)
end

"Compile one decoded equality atom; graph decoding and independent table checks are outside measurement."
function milp_construction_case(parameters)
    width = get(parameters, "width", 8)
    width > 0 || throw(ArgumentError("positive domain width required"))
    space = XB.NetworkSpace([0:width-1, 0:width-1]; slots=1, operators=(:eq,), constants=0:1)
    weights = BigInt[findfirst(==(:eq), space.operators), 1, 2, 0, 0, 3]
    program = XB.decode_network(space, weights)
    prepare = () -> program
    operation = program -> XB.compile_milp(program)
    verify = (program, result) -> begin
        result.domain_relations == 2 && result.operation_relations == 1 || return false
        payload = XB.bridge_payload(result)
        length(payload["binary_variables"]) == 2width + width^2 || return false
        # The published primitive equations must use the original domains and
        # describe the same local atom as its independent equality predicate.
        for a in 0:width-1, b in 0:width-1
            XB.satisfies(program, [a, b]) == (a == b) || return false
        end
        primitive_equality_oracle(payload, width)
    end
    (; prepare, operation, verify)
end
