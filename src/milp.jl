function exact_float(value::Integer)
    converted = Float64(value)
    isfinite(converted) && BigInt(converted) == value ||
        throw(ArgumentError("MILP reference requires exactly representable integer coefficients"))
    converted
end
integer_string(value::Float64) = string(BigInt(value))

"Register the existing CPE finite-domain and local-relation bridges."
function add_bridges!(model)
    MOI.Bridges.add_bridge(model, CPE.Bridges.Domain2MILPBridge{Float64})
    MOI.Bridges.add_bridge(model, CPE.Bridges.VectorDomain2MILPBridge{Float64})
    model
end

const ProgramConstraint = Union{
    MOI.ConstraintIndex{MOI.VariableIndex,CPE.Domain{Float64}},
    MOI.ConstraintIndex{MOI.VectorOfVariables,CPE.VectorDomain{Float64}},
    MOI.ConstraintIndex{MOI.ScalarAffineFunction{Float64},MOI.EqualTo{Float64}},
}

function emit_relations!(model, plan, variables, domain_values)
    sources = zeros(Int, length(plan.codebooks))
    domain_relations = operation_relations = 0
    constraints = ProgramConstraint[]
    sizehint!(constraints, length(plan.nodes) + 1)
    affine(variable) = MOI.ScalarAffineFunction([MOI.ScalarAffineTerm(1.0, variable)], 0.0)
    for (index, node) in enumerate(plan.nodes)
        if node.operator === :variable
            push!(constraints, MOI.add_constraint(model, variables[index],
                CPE.Domain(Set(domain_values[index]))))
            sources[node.data::Int] = variables[index].value
            domain_relations += 1
        elseif node.operator === :constant
            push!(constraints, MOI.add_constraint(model, affine(variables[index]),
                MOI.EqualTo(only(domain_values[index]))))
        else
            ports = [node.inputs; index]
            rows = Set{Vector{Float64}}()
            for row in node.rows
                push!(rows, [domain_values[port][column]
                    for (port, column) in zip(ports, row)])
            end
            push!(constraints, MOI.add_constraint(model, MOI.VectorOfVariables(variables[ports]),
                CPE.VectorDomain(length(ports), rows)))
            operation_relations += 1
        end
    end
    all(>(0), sources) || error("missing source port")
    push!(constraints, MOI.add_constraint(model, affine(variables[plan.root]), MOI.EqualTo(1.0)))
    (; sources, root=variables[plan.root].value, domain_relations, operation_relations, constraints)
end

# Validate before modifying a caller's model, including Float64 exactness. Source
# graph arrays are read-only by contract, but validation catches direct mutation.
function validate_milp(program)
    budget_boundary() do
        QC.validate_atomic_plan(program.plan)
    end
    # Convert each checked domain once before modifying the caller's model.
    # Local rows reuse these exact values; each emitted table still owns its rows.
    [exact_float.(node.domain) for node in program.plan.nodes]
end

"""Compile model + weights into an ordinary primitive MOI MILP.

The root is fixed to one. Projection onto the source variables equals network
satisfaction. Tables describe individual atoms only, never a whole constraint.
No solver, source recipe, constraint family or validation labels are required.
"""
function compile_milp(program::Program)
    domain_values = validate_milp(program)
    linear = MOI.Utilities.Model{Float64}()
    model = add_bridges!(MOI.Bridges.LazyBridgeOptimizer(linear))
    variables = MOI.add_variables(model, length(program.plan.nodes))
    emitted = emit_relations!(model, program.plan, variables, domain_values)
    (; linear, emitted.sources, emitted.root, emitted.domain_relations, emitted.operation_relations)
end
compile_milp(space::NetworkSpace, network) = compile_milp(decode_network(space, network))
compile_milp(space::QC.AtomicSearchSpace, weights) = compile_milp(decode_network(NetworkSpace(space), weights))

"""Bind a program to existing MOI source variables and add its local relations.

Use a LazyBridgeOptimizer with `add_bridges!` first. Returns handles for every
added graph constraint and auxiliary variable. Sources may repeat (aliases).
"""
function add_program!(model, program::Program, sources::AbstractVector{MOI.VariableIndex})
    length(sources) == length(program.plan.codebooks) || throw(DimensionMismatch("source variables"))
    domain_values = validate_milp(program)
    variables = MOI.VariableIndex[]
    auxiliaries = MOI.VariableIndex[]
    for node in program.plan.nodes
        if node.operator === :variable
            push!(variables, sources[node.data])
        else
            variable = MOI.add_variable(model)
            push!(variables, variable)
            push!(auxiliaries, variable)
        end
    end
    emitted = emit_relations!(model, program.plan, variables, domain_values)
    (; emitted..., auxiliaries)
end

"Portable integral sparse MILP, after the CPE bridges have actually run."
function bridge_payload(bridge)
    binary = Int[]
    equalities = Dict{String,Any}[]
    for (F, S) in MOI.get(bridge.linear, MOI.ListOfConstraintTypesPresent())
        if F === MOI.VariableIndex && S === MOI.ZeroOne
            append!(binary, [MOI.get(bridge.linear, MOI.ConstraintFunction(), c).value
                for c in MOI.get(bridge.linear, MOI.ListOfConstraintIndices{F,S}())])
        elseif F === MOI.ScalarAffineFunction{Float64} && S === MOI.EqualTo{Float64}
            for c in MOI.get(bridge.linear, MOI.ListOfConstraintIndices{F,S}())
                f = MOI.get(bridge.linear, MOI.ConstraintFunction(), c)
                s = MOI.get(bridge.linear, MOI.ConstraintSet(), c)
                coefficients = Dict{Int,BigInt}()
                for term in f.terms
                    coefficients[term.variable.value] = get(coefficients, term.variable.value, big(0)) +
                        BigInt(term.coefficient)
                end
                terms = [Dict("variable"=>i, "coefficient"=>string(coefficients[i]))
                    for i in sort!(collect(keys(coefficients))) if !iszero(coefficients[i])]
                push!(equalities, Dict("terms"=>terms, "constant"=>integer_string(f.constant),
                    "rhs"=>integer_string(s.value)))
            end
        else
            error("unexpected unbridged primitive: $F in $S")
        end
    end
    sort!(equalities; by=payload_digest)
    Dict("schema_version"=>"cpe-atomic-milp-witness/1",
        "decoder"=>"QUBOConstraints.decode_atomic_weights",
        "bridges"=>["CPE.Domain2MILPBridge", "CPE.VectorDomain2MILPBridge"],
        "variables"=>MOI.get(bridge.linear, MOI.NumberOfVariables()),
        "source_variables"=>bridge.sources, "root_variable"=>bridge.root,
        "binary_variables"=>sort!(binary), "equalities"=>equalities,
        "domain_relations"=>bridge.domain_relations,
        "operation_relations"=>bridge.operation_relations)
end

function restore_bridge(payload)
    payload["schema_version"] == "cpe-atomic-milp-witness/1" || throw(ArgumentError("bridge schema"))
    model = MOI.Utilities.Model{Float64}()
    variables = MOI.add_variables(model, payload["variables"])
    for index in payload["binary_variables"]
        MOI.add_constraint(model, variables[index], MOI.ZeroOne())
    end
    for equation in payload["equalities"]
        terms = [MOI.ScalarAffineTerm(exact_float(parse(BigInt, t["coefficient"])),
            variables[t["variable"]]) for t in equation["terms"]]
        f = MOI.ScalarAffineFunction(terms, exact_float(parse(BigInt, equation["constant"])))
        MOI.add_constraint(model, f, MOI.EqualTo(exact_float(parse(BigInt, equation["rhs"]))))
    end
    model
end
