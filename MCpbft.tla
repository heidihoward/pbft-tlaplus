---- MODULE MCpbft ----

EXTENDS pbft

\* Representing replicas as constants instead of integers allows us to use symmetry sets when checking safety properties with TLC
\* CONSTANT R0, R1, R2, R3
\* MC_R == {R0, R1, R2, R3}

\* Switch replicas to strings for easy Apalache compatibility

MC_R == 0..3

\* @type: Set(Int);
MC_ByzR == {}

MC_Tstamps == 1..3

MC_Views == 0..2

\* @type: Set(Int);
MC_Checkpoints == {}

====