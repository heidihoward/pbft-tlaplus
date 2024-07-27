---- MODULE MCpbft ----

EXTENDS pbft, Randomization

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

----

PBFT == INSTANCE pbft

MCViewChange(i) ==
    /\ views[i] + 1 \in Views
    /\ PBFT!ViewChange(i)

----

(* https://lamport.azurewebsites.net/tla/inductive-invariant.pdf *)

RPrepareProof == [
    preprepare : PrePrepareMessages,
    prepare : RandomSetOfSubsets(1, 2, PrepareMessages)]

RViewChangeMessages == [
    v : Views, 
    n : SeqNums \union {0}, 
    c : RandomSetOfSubsets(2, 3, CheckpointMessages), 
    p : RandomSetOfSubsets(2, 3, RPrepareProof), 
    i : R]

RNewViewMessages == [
    v : Views,
    vc : RandomSetOfSubsets(2, 2, RViewChangeMessages),
    o : RandomSetOfSubsets(2, 2, PrePrepareMessages),
    p : R]

RLoggedMessages == [
    request : RandomSetOfSubsets(2, 3, RequestMessages), 
    viewchange : RandomSetOfSubsets(2, 2, RViewChangeMessages),
    preprepare : RandomSetOfSubsets(1, 2, PrePrepareMessages),
    prepare : RandomSetOfSubsets(1, 2, PrepareMessages),
    commit : RandomSetOfSubsets(1, 2, CommitMessages),
    reply : RandomSetOfSubsets(1, 2, ReplyMessages),
    checkpoint : RandomSetOfSubsets(1, 2, CheckpointMessages)]

----

RMessages == [ 
    request : RandomSetOfSubsets(2, 2, RequestMessages), 
    viewchange : RandomSetOfSubsets(2, 2, RViewChangeMessages),
    preprepare : RandomSetOfSubsets(1, 2, PrePrepareWithRequestMessages),
    prepare : RandomSetOfSubsets(1, 2, PrepareMessages),
    commit : RandomSetOfSubsets(1, 2, CommitMessages),
    reply : RandomSetOfSubsets(1, 2, ReplyMessages),
    checkpoint : RandomSetOfSubsets(1, 2, CheckpointMessages),
    newview : RandomSetOfSubsets(1, 2, RNewViewMessages)]

----

EInit ==
    /\ msgs = [ 
            request |-> [t : Tstamps],
            preprepare |-> {},
            prepare |-> {},
            commit |-> {},
            reply |-> {},
            checkpoint |-> {},
            viewchange |-> {},
            newview |-> {}]
    /\ mlogs = [r \in R |-> [
            request |-> {},
            preprepare |-> {},
            prepare |-> {},
            commit |-> {},
            reply |-> {},
            checkpoint |-> {},
            viewchange |-> {}]]
    /\ vChange = [r \in R |-> FALSE]
    /\ views = [r \in R |-> 0]
    /\ states = [r \in R |-> 0]
    /\ sCheckpoint = [r \in R |-> {}]

RInit ==
    /\ msgs \in RMessages
    /\ mlogs \in [R -> RLoggedMessages]
    /\ vChange \in RandomSubset(2, [R -> BOOLEAN])
    /\ views \in RandomSubset(2, [R -> Views]) 
    /\ states \in RandomSubset(2, [R -> States])
    /\ sCheckpoint \in [R -> RandomSetOfSubsets(2, 2, CheckpointMessages)]

MCInit ==
    /\ 
       \/ EInit
       \/ RInit
    /\ TypeOK

=====
