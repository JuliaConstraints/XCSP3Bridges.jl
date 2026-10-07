"""Finite learnable operation networks and their CPE/MOI MILP compilation.

Reconstruction, not a recovered copy of the historical XCSP3Bridges module.
No constraint-specific recipe or semantic oracle runs in this package.
"""
module XCSP3Bridges

import QUBOConstraints as QC
import ConstraintProgrammingExtensions as CPE
import MathOptInterface as MOI
using SHA, TOML

export NetworkSpace, Network, Program, BudgetExceeded, NETWORK_VERSION
export network_count, network_at, network_rank, decode_network, satisfies, decision_domains
export network_payload, restore_network, load_witness, payload_digest
export compile_milp, bridge_payload, restore_bridge, add_program!, add_bridges!
export train, TrainingResult

const NETWORK_VERSION = "xcsp3bridges/structural-DAG-v1"
include("networks.jl")
include("milp.jl")
include("serialization.jl")
include("training.jl")

end
