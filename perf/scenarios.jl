import XCSP3Bridges as XB
import QUBOConstraints as QC
import MathOptInterface as MOI

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
