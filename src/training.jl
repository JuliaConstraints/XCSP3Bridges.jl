struct TrainingResult
    network::Union{Nothing,Network}
    mismatches::Union{Nothing,Int}
    candidates::Int
    rejected::Int
    resource_limited::Int
    status::Symbol
end

"""Bounded reference learner over public structural ranks, optionally seeded.

This is a small correctness/HPO baseline, not an efficient large-space optimizer.
`training_fit` means zero training mismatches, not generalization or minimality.
Initial decisions count toward the candidate budget and pass the normal decoder.
Invalid candidates and resource refusals remain separate.
"""
function train(space::NetworkSpace, assignments::AbstractVector, labels::AbstractVector{Bool};
        max_candidates::Integer=100, initial_weights=nothing, start_rank::Integer=0)
    0 < max_candidates <= typemax(Int) || throw(ArgumentError("positive candidate budget required"))
    start_rank >= 0 || throw(ArgumentError("negative start rank"))
    !isempty(assignments) && length(assignments) == length(labels) ||
        throw(ArgumentError("nonempty paired training corpus required"))
    for x in assignments
        length(x) == length(space.domains) || throw(DimensionMismatch("training assignment"))
        all(value isa Integer && value in domain for (value, domain) in zip(x, space.domains)) ||
            throw(ArgumentError("training assignment outside source domains"))
    end
    initial = initial_weights === nothing ? nothing : initial_weights isa Network ?
        initial_weights : Network(initial_weights)
    counts = nothing
    rank = big(start_rank)
    best = nothing; loss = nothing; rejected = limited = tried = 0
    while tried < max_candidates
        if tried == 0 && initial !== nothing
            candidate = initial
        else
            counts === nothing && (counts = rank_table(space))
            population = counts[(space.slots, 0)]
            if rank >= population
                status = start_rank > 0 ? :suffix_exhausted : limited > 0 ?
                    :space_exhausted_under_resource_limits : :space_exhausted
                return TrainingResult(best, loss, tried, rejected, limited, status)
            end
            # The public unrank implementation uses the same table; reuse it below.
            candidate = network_at(space, rank, counts)
            rank += 1
        end
        tried += 1
        program = try
            decode_network(space, candidate)
        catch e
            if e isa BudgetExceeded
                limited += 1
            elseif e isa Union{ArgumentError, DimensionMismatch, BoundsError}
                rejected += 1
            else
                rethrow()
            end
            nothing
        end
        program === nothing && continue
        misses = count(satisfies(program, x) != label for (x, label) in zip(assignments, labels))
        if loss === nothing || misses < loss
            best = Network(candidate.weights); loss = misses
        end
        misses == 0 && return TrainingResult(best, loss, tried, rejected, limited, :training_fit)
    end
    TrainingResult(best, loss, tried, rejected, limited, :budget_exhausted)
end
