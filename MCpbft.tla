---- MODULE MCpbft ----

EXTENDS pbft

\* Representing replicas as constants instead of integers allows us to use symmetry sets when checking safety properties with TLC
\* CONSTANT R0, R1, R2, R3
\* MC_R == {R0, R1, R2, R3}

\* Switch replicas to strings for easy Apalache compatibility

MC_R == 0..3
MC_ByzR == {2}

MC_Tstamps == 1..2

MC_Views == {0}

====