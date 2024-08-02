---- MODULE APApbft ----
\* PBFT model for checking with Apalache

EXTENDS pbft

\* Set of replicas
MC_R == 0..3

\* Set of requests which are byzantine
\* @type: Set(Int);
MC_ByzR == {}

MC_Tstamps == 1..3

MC_Views == 0..2

\* @type: Set(Int);
MC_Checkpoints == {}

ConstInit ==
    /\ ByzR = MC_ByzR
    /\ R = MC_R
    /\ Checkpoints = MC_Checkpoints

====