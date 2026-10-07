using Test, TOML
import XCSP3Bridges as XB
import QUBOConstraints as QC
import MathOptInterface as MOI
import HiGHS

function projected_check(compilation, assignments, expected)
    primitive = XB.restore_bridge(XB.bridge_payload(compilation))
    variables = MOI.get(primitive, MOI.ListOfVariableIndices())
    fixes = [MOI.add_constraint(primitive,
        MOI.ScalarAffineFunction([MOI.ScalarAffineTerm(1.0, variables[i])], 0.0),
        MOI.EqualTo(0.0)) for i in compilation.sources]
    optimizer = HiGHS.Optimizer()
    MOI.set(optimizer, MOI.Silent(), true)
    MOI.set(optimizer, MOI.RawOptimizerAttribute("threads"), 1)
    MOI.set(optimizer, MOI.TimeLimitSec(), 5.0)
    map = MOI.copy_to(optimizer, primitive)
    for (x, label) in zip(assignments, expected)
        for (fix, value) in zip(fixes, x)
            MOI.set(optimizer, MOI.ConstraintSet(), map[fix], MOI.EqualTo(Float64(value)))
        end
        MOI.optimize!(optimizer)
        @test MOI.get(optimizer, MOI.TerminationStatus()) === (label ? MOI.OPTIMAL : MOI.INFEASIBLE)
    end
end

@testset "Reconstructed XCSP3Bridges" begin
    @testset "Structural ranks and Boolean closure" begin
        for (slots, population) in ((0, 1), (1, 9), (2, 113))
            s = XB.NetworkSpace([0:1]; slots, operators=(:not, :and), constants=0:1)
            @test XB.network_count(s) == population
            seen = Set{Tuple}()
            for rank in 0:population-1
                network = XB.network_at(s, rank)
                @test XB.network_rank(s, network) == rank
                @test !(Tuple(network.weights) in seen)
                push!(seen, Tuple(network.weights))
                program = XB.decode_network(s, network)
                @test all(XB.satisfies(program, [x]) isa Bool for x in 0:1)
            end
            @test XB.network_at(s, 0).weights[end] == 1
            @test XB.satisfies(XB.decode_network(s, XB.network_at(s, 0)), [1])
            @test !XB.satisfies(XB.decode_network(s, XB.network_at(s, 0)), [0])
            @test_throws BoundsError XB.network_at(s, -1)
            @test_throws BoundsError XB.network_at(s, population)
        end
        s = XB.NetworkSpace([0:1, 0:1]; slots=1, operators=(Symbol("if"),), constants=0:1)
        @test XB.network_count(s) == 32
        for rank in 0:31
            @test XB.network_rank(s, XB.network_at(s, rank)) == rank
            @test XB.decode_network(s, XB.network_at(s, rank)) isa XB.Program
        end
        # No sources: only an enabled constant can provide a root.
        s = XB.NetworkSpace([]; slots=1, operators=(:constant,), constants=0:1)
        @test XB.network_count(s) == 2
        @test !XB.satisfies(XB.decode_network(s, XB.network_at(s, 0)), Int[])
        @test XB.satisfies(XB.decode_network(s, XB.network_at(s, 1)), Int[])
        for literals in (-2:2, -2:-1, 1:3)
            s = XB.NetworkSpace([0:1]; slots=1, operators=(:constant,), constants=literals)
            for rank in 0:Int(XB.network_count(s))-1
                @test XB.network_rank(s, XB.network_at(s, rank)) == rank
            end
        end
    end

    @testset "Weights, ownership, errors and budgets" begin
        domains = [[0, 1], [0, 1]]
        s = XB.NetworkSpace(domains; slots=1, operators=(:eq,), constants=0:1)
        domains[1][1] = 99
        @test s.domains[1] == [0, 1]
        eq = BigInt[findfirst(==(:eq), s.operators), 1, 2, 0, 0, 3]
        network = XB.Network(eq)
        eq[1] = 0
        @test network.weights[1] != 0
        p = XB.decode_network(s, network)
        network.weights[2] = 2
        @test !XB.satisfies(p, [0, 1])
        @test XB.satisfies(p, Dict(:x1=>0, :x2=>0))
        @test_throws ArgumentError XB.satisfies(p, [2, 0])
        @test_throws ArgumentError XB.satisfies(p, [0.0, 0.0])
        @test_throws DimensionMismatch XB.satisfies(p, [0])
        @test_throws DimensionMismatch XB.decode_network(s, BigInt[1])
        @test_throws ArgumentError XB.decode_network(s, BigInt[0, 1, 0, 0, 0, 1])
        @test_throws ArgumentError XB.decode_network(s, BigInt[2, 3, 1, 0, 0, 3])
        @test_throws ArgumentError XB.decode_network(s, BigInt[0, 0, 0, 0, 0, 3])
        @test_throws ArgumentError XB.decode_network(s, XB.Network(BigInt[0, 0, 0, 0, 0, 1]; version="lost-version"))
        @test_throws ArgumentError XB.NetworkSpace([[0, 0]])
        @test_throws ArgumentError XB.NetworkSpace([[0.0, 1.0]])
        @test_throws ArgumentError XB.NetworkSpace([0:1]; operators=(:unknown,))
        limited = XB.NetworkSpace([0:2, 0:2]; slots=1, operators=(:eq,), max_local_rows=8)
        @test_throws XB.BudgetExceeded XB.decode_network(limited, BigInt[2, 1, 2, 0, 0, 3])
        @test_throws XB.BudgetExceeded XB.network_count(XB.NetworkSpace([0:1]; slots=2, max_rank_states=5))
        @test_throws XB.BudgetExceeded XB.network_count(XB.NetworkSpace([0:1]; slots=1, max_rank_bits=1))
        nonsymmetric = XB.NetworkSpace([0:1]; slots=1, constants=1:2)
        @test_throws ArgumentError XB.decode_network(nonsymmetric, BigInt[1, 0, 0, 0, -1, 2])
        @test XB.decode_network(nonsymmetric, BigInt[0, 0, 0, 0, 0, 1]) isa XB.Program
    end

    @testset "Portable weights and independent import" begin
        s = XB.NetworkSpace([0:2, -1:1]; slots=1, operators=(:gt,), constants=-2:2)
        weights = BigInt[2, 1, 2, 0, 0, 3]
        payload = XB.network_payload(s, weights)
        restored, net = XB.restore_network(TOML.parse(sprint(io -> TOML.print(io, payload))))
        @test restored.domains == s.domains
        @test restored.constants == s.constants
        @test net.weights == weights
        @test XB.network_rank(restored, net) == XB.network_rank(s, weights)
        @test XB.bridge_payload(XB.compile_milp(restored, net)) == XB.bridge_payload(XB.compile_milp(s, weights))
        payload["model"]["hidden_recipe"] = "forbidden"
        @test_throws ArgumentError XB.restore_network(payload)
        huge = XB.NetworkSpace([[big(2)^53+1]]; slots=1, operators=(:eq,), constants=0:1)
        p = XB.decode_network(huge, BigInt[2, 1, 1, 0, 0, 2])
        @test_throws ArgumentError XB.compile_milp(p)
    end

    @testset "MILP projection, shared wires and unused sources" begin
        s = XB.NetworkSpace([0:2, 0:2]; slots=1, operators=(:eq,), constants=0:1)
        weights = BigInt[2, 1, 2, 0, 0, 3]
        xs = [collect(x) for x in Iterators.product(0:2, 0:2)] |> vec
        projected_check(XB.compile_milp(s, weights), xs, [x[1] == x[2] for x in xs])
        # Duplicate predecessor ports must keep aliases, including rows with
        # incompatible port values that the shared variable makes infeasible.
        shared = BigInt[2, 1, 1, 0, 0, 3]
        projected_check(XB.compile_milp(s, shared), [[0, 0], [1, 2], [3, 0], [0, 3]], [true, true, false, false])
        # Bind to a caller's source variables; source aliases are allowed too.
        linear = MOI.Utilities.Model{Float64}()
        model = XB.add_bridges!(MOI.Bridges.LazyBridgeOptimizer(linear))
        x = MOI.add_variable(model)
        emitted = XB.add_program!(model, XB.decode_network(s, weights), [x, x])
        @test length(emitted.auxiliaries) == 1
        @test emitted.sources == [x.value, x.value]
        compilation = (; linear, emitted.sources, emitted.root, emitted.domain_relations, emitted.operation_relations)
        projected_check(compilation, [[0, 0], [2, 2]], [true, true])
        for value in (0, 1)
            constant = XB.NetworkSpace([]; slots=1, operators=(:constant,), constants=0:1)
            projected_check(XB.compile_milp(constant, BigInt[1, 0, 0, 0, value, 1]), [Int[]], [value == 1])
        end
    end

    @testset "Small learner and failure classification" begin
        s = XB.NetworkSpace([0:1]; slots=1, operators=(:not, :and), constants=0:1)
        result = XB.train(s, [[0], [1]], Bool[true, false]; max_candidates=9)
        @test result.status === :training_fit
        @test result.mismatches == 0
        @test all(XB.satisfies(XB.decode_network(s, result.network), x) == y
            for (x, y) in zip([[0], [1]], [true, false]))
        seeded = XB.train(s, [[0], [1]], Bool[true, false]; max_candidates=1, initial_weights=result.network)
        @test seeded.status === :training_fit && seeded.candidates == 1
        @test XB.train(s, [[0], [1]], Bool[true, false]; max_candidates=1).status === :budget_exhausted
        @test XB.train(s, [[0]], Bool[false]; max_candidates=1,
            initial_weights=BigInt[0, 0, 0, 0, 0, 2]).rejected == 1
        limited = XB.NetworkSpace([0:1]; slots=1, operators=(:and,), max_local_rows=3)
        @test XB.train(limited, [[0]], Bool[false]; max_candidates=1,
            initial_weights=BigInt[2, 1, 1, 0, 0, 2]).resource_limited == 1
        @test_throws ArgumentError XB.train(s, [[2]], Bool[false])
        @test_throws ArgumentError XB.train(s, Vector{Int}[], Bool[])
    end
end
