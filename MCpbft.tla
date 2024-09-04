---- MODULE MCpbft ----

EXTENDS APApbft, Randomization

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
    preprepare : RandomSetOfSubsets(1, 2, PrePrepareMessages),
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
    /\ Inv

-------

\* This is Heidi's definition of GenerateO moved out of pbft. However, Apalache
\* does not support  (mins+1)..maxs  when mins and maxs are non-constant.
\* Moreover, Apalache does not support re-defining this non-zero arity operator,
\* which is why the more complex definition is now in pbft and the simpler one
\* below.
\* @type: (Set ($viewchangeMsgs), Int, Int) => Set ($preprepareMsgs);
MC_GenerateO(V,i,v) ==
    LET mins == Max0(UNION {{cp.n: cp \in vcm.c}: vcm \in V}) 
        ppms == UNION {{pp.preprepare: pp \in vcm.p}: vcm \in V}
        maxs == Max0({ppm.n: ppm \in ppms}) IN
    {[v |-> v, p |-> i, n |-> sn, d |-> GetDigest(ppms,sn)] : sn \in (mins+1)..maxs}

-------


MCRandomSetOfSubsets(S) ==
    (* Up to 2^8 subsets of S. *)
    IF Cardinality(S) <= 8
    \* Exhaustively generate all subsets up to and including 512 elements.
    THEN SUBSET S
    \* Constraints RandomSetOfSubsets(k,n,S) operator:
    \* k < 2^|S| and n \in 0..Cardinality(S)
    \* see https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/Randomization.tla
    ELSE RandomSetOfSubsets(2^8, Cardinality(S) \div 2, S)

SimInjectViewChange(i) ==
    /\ \E v \in Views, n \in (SeqNums \cup {0}), 
            c \in MCRandomSetOfSubsets(msgs.checkpoint), 
            p \in MCRandomSetOfSubsets([preprepare : msgs.preprepare, prepare : MCRandomSetOfSubsets(msgs.prepare)]) :
        \* Any replica that receive a view change message will check that the checkpoint/prepare proofs are valid
        \* Therefore, we do not need to brother injecting view change messages with invalid proofs
        /\ ValidCheckpointProof(c, n)
        /\ \A pp \in p: ValidPrepareProof(pp, n)
        /\ msgs' = [msgs EXCEPT !.viewchange = @ \cup {[
            v |-> v,
            n |-> n,
            c |-> c,
            p |-> p,
            i |-> i]}]
    /\ UNCHANGED <<mlogs, views, states, sCheckpoint, vChange>>

SimInjectNewView(i) ==
    /\ \E v \in Views, vc \in MCRandomSetOfSubsets(msgs.viewchange), o \in MCRandomSetOfSubsets(msgs.preprepare) : 
        /\ i = v % N
        /\ \A vcm \in vc: ValidViewChange(vcm, v)
        /\ o = GenerateO(vc, i, v)
        /\ msgs' = [msgs EXCEPT !.newview = @ \cup {[
            v |-> v,
            vc |-> vc,
            o |-> o,
            p |-> i]}]
    /\ UNCHANGED <<mlogs, views, states, sCheckpoint, vChange>>

=====
