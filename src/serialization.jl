payload_digest(payload) = bytes2hex(sha256(sprint(io -> TOML.print(io, payload; sorted=true))))

function atomic_payload(space, weights)
    all(b -> b isa QC.StructuredCodebook, space.codebooks) ||
        throw(ArgumentError("portable witnesses require structured source codebooks"))
    Dict("node_slots"=>space.node_slots, "constant_bound"=>string(space.constant_bound),
        "operators"=>string.(space.operators), "max_nodes"=>space.max_nodes,
        "max_local_rows"=>space.max_local_rows, "max_total_rows"=>space.max_total_rows,
        "max_value_bits"=>space.max_value_bits, "max_depth"=>space.max_depth,
        "sources"=>[Dict("variable"=>string(b.variable), "values"=>string.(b.values),
            "encoding"=>string(b.encoding), "coefficient_bound"=>string(b.coefficient_bound))
            for b in space.codebooks])
end

"Portable model and every integer decision. No cached plan or target predicate."
function network_payload(space::NetworkSpace, network::Network)
    network.version == NETWORK_VERSION || throw(ArgumentError("network version mismatch"))
    network_payload(space, network.weights)
end
function network_payload(space::NetworkSpace, weights::AbstractVector{<:Integer})
    decode_network(space, weights)
    Dict("schema_version"=>"xcsp3bridges-witness/1", "network_version"=>NETWORK_VERSION,
        "model"=>atomic_payload(space.atomic, weights), "weights"=>string.(weights),
        "constants"=>string.([first(space.constants), last(space.constants)]),
        "max_rank_states"=>space.limits.max_rank_states, "max_rank_bits"=>space.limits.max_rank_bits)
end

function restore_atomic(model)
    Set(keys(model)) == Set(["node_slots", "constant_bound", "operators", "max_nodes",
        "max_local_rows", "max_total_rows", "max_value_bits", "max_depth", "sources"]) ||
        throw(ArgumentError("unexpected model fields"))
    books = [QC.structured_codebook(Symbol(s["variable"]), parse.(BigInt, s["values"]);
        encoding=Symbol(s["encoding"]), coefficient_bound=parse(BigInt, s["coefficient_bound"]))
        for s in model["sources"]]
    budget_boundary() do
        QC.AtomicSearchSpace(books; node_slots=model["node_slots"],
            constant_bound=parse(BigInt, model["constant_bound"]), operators=Symbol.(model["operators"]),
            max_nodes=model["max_nodes"], max_local_rows=model["max_local_rows"],
            max_total_rows=model["max_total_rows"], max_value_bits=model["max_value_bits"],
            max_depth=model["max_depth"])
    end
end

"""Restore a new witness or import a recovered Q12 `atomic-search-witness/1`.

Top-level qualification, QUBO and MILP data may accompany recovered records;
none is passed to the decoder. Validation compares labels outside this package.
"""
function restore_network(payload::AbstractDict)
    schema = payload["schema_version"]
    schema in ("xcsp3bridges-witness/1", "atomic-search-witness/1") ||
        throw(ArgumentError("unknown network schema"))
    atomic = restore_atomic(payload["model"])
    if schema == "xcsp3bridges-witness/1"
        payload["network_version"] == NETWORK_VERSION || throw(ArgumentError("network version mismatch"))
        endpoints = parse.(BigInt, payload["constants"])
        length(endpoints) == 2 || throw(ArgumentError("literal interval endpoints"))
        space = NetworkSpace(atomic; constants=endpoints[1]:endpoints[2],
            max_rank_states=payload["max_rank_states"], max_rank_bits=payload["max_rank_bits"])
    else
        space = NetworkSpace(atomic)
    end
    network = Network(parse.(BigInt, payload["weights"]))
    decode_network(space, network)
    space, network
end
load_witness(path::AbstractString) = restore_network(TOML.parsefile(path))
