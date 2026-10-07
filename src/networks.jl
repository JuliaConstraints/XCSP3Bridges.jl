"A resource refusal, never a claim that a constraint cannot be represented."
struct BudgetExceeded <: Exception
    stage::Symbol
    requested::BigInt
    limit::BigInt
end
Base.showerror(io::IO, e::BudgetExceeded) = print(io, "unsupported_under_budget: ",
    e.stage, " requested ", e.requested, " > ", e.limit)

function budget_boundary(f)
    try
        f()
    catch e
        e isa QC.CompilationLimit && throw(BudgetExceeded(e.stage, e.requested, e.limit))
        rethrow()
    end
end

const UNARY = (:neg, :abs, :sqr, :not)
const BINARY = (:add, :sub, :mul, :div, :mod, :pow, :dist, :min, :max,
    :eq, :ne, :lt, :le, :ge, :gt, :and, :or, :xor, :iff, :imp,
    :div_total, :mod_total, :pow_total, :pow_defined)
arity(op) = op === :constant ? 0 : op in UNARY ? 1 : op in BINARY ? 2 :
    op === Symbol("if") ? 3 : throw(ArgumentError("unsupported operation $op"))

"""Owned finite source domains, operation alphabet, literal interval and budgets.

There are five integer decisions per slot (operation, three ports, literal) and
one root decision. Disabled slots have an all-zero payload. Array fields must be
treated as read-only. `operators` in the domain constructor includes `:constant`.
The rank interface enumerates structurally valid graphs, including semantically
invalid or resource-limited ones, without looking at any target constraint.
"""
struct NetworkSpace
    domains::Vector{Vector{BigInt}}
    slots::Int
    operators::Vector{Symbol}
    constants::UnitRange{BigInt}
    limits::NamedTuple
    atomic::QC.AtomicSearchSpace
end

function NetworkSpace(atomic::QC.AtomicSearchSpace;
        constants=-atomic.constant_bound:atomic.constant_bound,
        max_rank_states::Integer=100000, max_rank_bits::Integer=1000000)
    constants isa AbstractUnitRange{<:Integer} && !isempty(constants) ||
        throw(ArgumentError("nonempty integer literal interval required"))
    max(abs(big(first(constants))), abs(big(last(constants)))) <= atomic.constant_bound ||
        throw(ArgumentError("literal interval exceeds atomic bound"))
    0 < max_rank_states <= typemax(Int) && 0 < max_rank_bits <= typemax(Int) ||
        throw(ArgumentError("positive representable ranking budgets required"))
    owned = deepcopy(atomic)
    limits = (; max_nodes=owned.max_nodes, max_local_rows=owned.max_local_rows,
        max_total_rows=owned.max_total_rows, max_value_bits=owned.max_value_bits,
        max_depth=owned.max_depth, max_rank_states=Int(max_rank_states),
        max_rank_bits=Int(max_rank_bits))
    NetworkSpace([BigInt.(b.values) for b in owned.codebooks], owned.node_slots,
        copy(owned.operators), big(first(constants)):big(last(constants)), limits, owned)
end

function NetworkSpace(domains; slots::Integer=1,
        operators=(:not, :and, :or, :eq, :lt, :add, :sub), constants=-1:1,
        max_rank_states::Integer=100000, max_rank_bits::Integer=1000000, kwargs...)
    constants isa AbstractUnitRange{<:Integer} && !isempty(constants) ||
        throw(ArgumentError("nonempty integer literal interval required"))
    ops = Symbol[operators...]
    allunique(ops) || throw(ArgumentError("duplicate operators"))
    :constant in ops || pushfirst!(ops, :constant)
    books = [QC.structured_codebook(Symbol("x", i), collect(values); encoding=:domain_wall)
        for (i, values) in enumerate(domains)]
    atomic = budget_boundary() do
        QC.AtomicSearchSpace(books; node_slots=slots,
            constant_bound=max(abs(big(first(constants))), abs(big(last(constants)))),
            operators=ops, kwargs...)
    end
    NetworkSpace(atomic; constants, max_rank_states, max_rank_bits)
end

"Plain integer decisions, with an explicit reconstructed numbering version."
struct Network
    weights::Vector{BigInt}
    version::String
    Network(weights::AbstractVector{<:Integer}; version=NETWORK_VERSION) =
        new(BigInt.(weights), String(version))
end

"Decoded, owned operation graph; no callback, family identifier or validation labels."
struct Program
    plan::QC.AtomicPlan
end

function decode_network(space::NetworkSpace, network::Network)
    network.version == NETWORK_VERSION || throw(ArgumentError("network version mismatch"))
    decode_network(space, network.weights)
end
function decode_network(space::NetworkSpace, weights::AbstractVector{<:Integer})
    length(weights) == 5space.slots + 1 || throw(DimensionMismatch("wrong decision count"))
    for slot in 1:space.slots
        at = 5(slot - 1)
        code = weights[at + 1]
        if 1 <= code <= length(space.operators) && space.operators[Int(code)] === :constant
            weights[at + 5] in space.constants || throw(ArgumentError("literal outside space interval"))
        end
    end
    budget_boundary() do
        Program(QC.decode_atomic_weights(space.atomic, weights))
    end
end

function satisfies(program::Program, assignment::AbstractVector)
    length(assignment) == length(program.plan.codebooks) ||
        throw(DimensionMismatch("wrong source assignment dimension"))
    all(x -> x isa Integer, assignment) || throw(ArgumentError("integer assignment required"))
    data = Dict(b.variable => value for (b, value) in zip(program.plan.codebooks, assignment))
    satisfies(program, data)
end
function satisfies(program::Program, assignment::AbstractDict)
    for book in program.plan.codebooks
        haskey(assignment, book.variable) && assignment[book.variable] isa Integer &&
            assignment[book.variable] in book.values || throw(ArgumentError("assignment outside source domains"))
    end
    QC.atomic_values(program.plan, assignment)[program.plan.root] == 1
end

"Independent optimizer bounds; decoding also checks causality, arity and types."
function decision_domains(space::NetworkSpace)
    domains = QC.atomic_decision_domains(space.atomic)
    for slot in 1:space.slots
        # Zero remains admissible in disabled/nonconstant slots even if not a literal.
        domains[5slot] = (min(big(0), first(space.constants)), max(big(0), last(space.constants)))
    end
    domains
end

literal_count(space) = last(space.constants) - first(space.constants) + 1
choices(space, available) = sum(op === :constant ? literal_count(space) : big(available)^arity(op)
    for op in space.operators; init=big(0))

# C(r,a) counts suffixes with r slots left and a active earlier slots. Disabled
# first; then operator order, lexicographic predecessor tuples and root order.
# Only a triangular O(slots^2) table is built, never the graph population.
function rank_table(space::NetworkSpace)
    states = div((big(space.slots) + 1) * (space.slots + 2), 2)
    states <= space.limits.max_rank_states ||
        throw(BudgetExceeded(:rank_states, states, big(space.limits.max_rank_states)))
    counts = Dict{Tuple{Int,Int},BigInt}()
    n = length(space.domains)
    for a in 0:space.slots
        counts[(0, a)] = big(n + a)
    end
    for r in 1:space.slots, a in 0:(space.slots - r)
        value = counts[(r - 1, a)] + choices(space, n + a) * counts[(r - 1, a + 1)]
        bits = ndigits(value; base=2)
        bits <= space.limits.max_rank_bits ||
            throw(BudgetExceeded(:rank_bits, big(bits), big(space.limits.max_rank_bits)))
        counts[(r, a)] = value
    end
    counts
end

network_count(space::NetworkSpace) = rank_table(space)[(space.slots, 0)]

# Literal zero first (when allowed), then the remaining interval in ascending order.
function literal_at(space, index)
    lo, hi = first(space.constants), last(space.constants)
    0 <= index < literal_count(space) || throw(BoundsError(space.constants, index))
    if lo <= 0 <= hi
        index == 0 && return big(0)
        value = lo + index - 1
        return value >= 0 ? value + 1 : value
    end
    lo + index
end
function literal_rank(space, value)
    value in space.constants || throw(ArgumentError("literal outside space interval"))
    lo, hi = first(space.constants), last(space.constants)
    lo <= 0 <= hi ? (value == 0 ? big(0) : value < 0 ? value - lo + 1 : value - lo) : value - lo
end

"Unrank a structural graph; rank zero selects the first source if one exists."
function network_at(space::NetworkSpace, rank::Integer)
    network_at(space, rank, rank_table(space))
end
function network_at(space::NetworkSpace, rank::Integer, counts)
    0 <= rank < counts[(space.slots, 0)] || throw(BoundsError(space, rank))
    rank = big(rank)
    weights = zeros(BigInt, 5space.slots + 1)
    available = collect(1:length(space.domains))
    active = 0
    for slot in 1:space.slots
        r = space.slots - slot
        disabled = counts[(r, active)]
        if rank < disabled
            continue
        end
        rank -= disabled
        suffix = counts[(r, active + 1)]
        ordinal, rank = divrem(rank, suffix)
        at = 5(slot - 1)
        for (code, op) in enumerate(space.operators)
            width = op === :constant ? literal_count(space) : big(length(available))^arity(op)
            if ordinal >= width
                ordinal -= width
                continue
            end
            weights[at + 1] = code
            if op === :constant
                weights[at + 5] = literal_at(space, ordinal)
            else
                for port in arity(op):-1:1
                    ordinal, digit = divrem(ordinal, length(available))
                    weights[at + 1 + port] = available[Int(digit) + 1]
                end
            end
            push!(available, length(space.domains) + slot)
            active += 1
            break
        end
    end
    weights[end] = available[Int(rank) + 1]
    Network(weights)
end

"Rank integer decisions; validates structural rules without a target predicate."
function network_rank(space::NetworkSpace, network::Network)
    network.version == NETWORK_VERSION || throw(ArgumentError("network version mismatch"))
    network_rank(space, network.weights)
end
function network_rank(space::NetworkSpace, weights::AbstractVector{<:Integer})
    length(weights) == 5space.slots + 1 || throw(DimensionMismatch("wrong decision count"))
    counts = rank_table(space)
    rank = big(0)
    available = collect(1:length(space.domains))
    active = 0
    for slot in 1:space.slots
        at = 5(slot - 1); code = weights[at + 1]; r = space.slots - slot
        0 <= code <= length(space.operators) || throw(ArgumentError("invalid operator decision"))
        if code == 0
            all(iszero, weights[at + 2:at + 5]) || throw(ArgumentError("disabled slot has payload"))
            continue
        end
        rank += counts[(r, active)]
        op = space.operators[Int(code)]
        ordinal = sum(prev === :constant ? literal_count(space) : big(length(available))^arity(prev)
            for prev in space.operators[1:Int(code) - 1]; init=big(0))
        localindex = big(0)
        for port in 1:3
            predecessor = weights[at + 1 + port]
            if port <= arity(op)
                digit = findfirst(==(predecessor), available)
                digit === nothing && throw(ArgumentError("invalid predecessor"))
                localindex = localindex * length(available) + digit - 1
            else
                iszero(predecessor) || throw(ArgumentError("unused port must be zero"))
            end
        end
        if op === :constant
            localindex = literal_rank(space, weights[at + 5])
        else
            iszero(weights[at + 5]) || throw(ArgumentError("nonconstant literal must be zero"))
        end
        rank += (ordinal + localindex) * counts[(r, active + 1)]
        push!(available, length(space.domains) + slot)
        active += 1
    end
    root = findfirst(==(weights[end]), available)
    root === nothing && throw(ArgumentError("invalid root"))
    rank + root - 1
end
