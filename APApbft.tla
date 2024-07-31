---- MODULE APApbft ----

EXTENDS pbft

MC_R == 0..3

\* @type: Set(Int);
MC_ByzR == {}

MC_Tstamps == 1..3

MC_Views == 0..2

\* @type: Set(Int);
MC_Checkpoints == {}

====