---- MODULE pbft ----
\* This TLA+ specification describes the normal case operation of Practical Byzantine Fault Tolerance protocol.
\* See https://www.pmg.csail.mit.edu/papers/osdi99.pdf for a full description of the protocol.
\* This specification can be checked with TLC and Apalache (https://apalache.informal.systems/). Note that typechecking with Apalache requires the --features=no-rows flag.
\* This iteration of the specification is significantly simplified from the original paper.
\* We make the following simplifying assumptions:
\* - no view changes, 1 fixed primary (node R1) 
\* - no byzantine primaries
\* - no liveness properties
\* - dummy requests
\* - one client with concurrent requests
\* - no garbage collection/checkpointing (Sec. 4.3)

EXTENDS Integers, FiniteSets, TLC

\* Set of replicas
\* Castro & Liskov 4 "We denote the set of replicas by R and identify each replica using an integer in {0,..|R|-1}."
CONSTANT 
\* @type: Set(Int);
    R

N == Cardinality(R)
F == (N - 1) \div 3

\* Castro & Liskov 4 "For simplicity, we assume N=3F+1 where F is the maximum number of replicas that may be faulty."
ASSUME N = 3*F + 1

\* Don't include the primary in the symmetry set
Symmetry == Permutations(R)

\* Byzantine replicas (backups only)
CONSTANT
\* @type: Set(Int);    
    ByzR

ASSUME ByzR \subseteq R

\* Set of request timestamps
\* We use just natural numbers as there's a single client
Tstamps == Nat

\* Set of sequence numbers
\* Bounding sequence numbers to the total number of requests
SeqNums == Tstamps

\* Sequence numbers to checkpoint at. An empty set means checkpointing is disabled
CONSTANT 
    \* @type: Set(Int);  
    Checkpoints 

ASSUME Checkpoints \subseteq SeqNums

\* Set of services states
\* We use the sequence number of the last request as the service state
States == SeqNums \union {0}

\* Set of results that clients can receive
\* Our dummy app will return the request sequence number
Results == SeqNums

\* Set of possible views
Views == Nat

\* RequestDigest takes a client request and returns a unique identifier
\* Since we are assuming timestamps are unique, we can use them as the digest
\* @type: [ t : Int ] => Int;
RequestDigest(m) == m.t

\* Set of possible request digests
RequestDigests == Tstamps

\* StateDigest takes a replica state and returns a unique identifier
\* Currently, we are just using the state itself as the digest
\* @type: Int => Int;
StateDigest(s) == s

\* Set of possible state digests
StateDigests == States

\* The following definitions describe all possible messages

RequestMessages == 
    [t : Tstamps]

\* We distinguish between two types of preprepare message, those with a piggybacked client request and those without

PrePrepareWithRequestMessages == [
    v: Views, 
    p : R, 
    n : SeqNums, 
    d : RequestDigests, 
    m : RequestMessages]

PrePrepareMessages == [
    v: Views, 
    p : R, 
    n : SeqNums, 
    d : RequestDigests]

PrepareMessages == [
    v : Views, 
    i : R, 
    n : SeqNums, 
    d : RequestDigests]

CommitMessages ==[
    v : Views, 
    i : R, 
    n : SeqNums, 
    d : RequestDigests]

ReplyMessages ==[
    v : Views, 
    i : R, 
    t : Tstamps, 
    r: Results]

CheckpointMessages ==[
    n : SeqNums, 
    d : StateDigests, 
    i : R]

PrepareProof == [
    preprepare : PrePrepareMessages,
    prepare : SUBSET PrepareMessages]

ViewChangeMessages == [
    v : Views, 
    n : SeqNums \union {0}, 
    c : SUBSET CheckpointMessages, 
    p : SUBSET PrepareProof, 
    i : R]

NewViewMessages == [
    v : Views,
    vc : SUBSET ViewChangeMessages,
    o : SUBSET PrePrepareMessages,
    p : R]

Messages == [ 
    request : SUBSET RequestMessages, 
    preprepare : SUBSET PrePrepareWithRequestMessages,
    prepare : SUBSET PrepareMessages,
    commit : SUBSET CommitMessages,
    reply : SUBSET ReplyMessages,
    checkpoint : SUBSET CheckpointMessages,
    viewchange : SUBSET ViewChangeMessages,
    newview : SUBSET NewViewMessages]

LoggedMessages == [
    request : SUBSET RequestMessages, 
    preprepare : SUBSET PrePrepareMessages,
    prepare : SUBSET PrepareMessages,
    commit : SUBSET CommitMessages,
    reply : SUBSET ReplyMessages,
    checkpoint : SUBSET CheckpointMessages,
    viewchange : SUBSET ViewChangeMessages]

\* Set of all messages ever sent
\* Note that messages are never removed from msgs
\* All messages are modelled as multicasted to all replicas

\* @typeAlias: requestMsgs = [ t : Int ];
\* @typeAlias: preprepareMsgsWithRequest = [ v : Int, p : Int, n : Int, d : Int,  m : [ t : Int ] ];
\* @typeAlias: preprepareMsgs = [ v : Int, p : Int, n : Int, d : Int];
\* @typeAlias: prepareMsgs = [ v : Int, i : Int, n : Int, d : Int ];
\* @typeAlias: commitMsgs = [ v : Int, i : Int, n : Int, d : Int ];
\* @typeAlias: replyMsgs = [ v : Int, i : Int, t : Int, r : Int ];
\* @typeAlias: checkpointMsgs = [ n : Int, d : Int, i : Int ];
\* @typeAlias: viewchangeMsgs = [ v : Int, n : Int, c : Set ([ n : Int, d : Int, i : Int ]), p : Set ([ preprepare : $preprepareMsgs, prepare : Set ($prepareMsgs) ]), i : Int ];
\* @typeAlias: newviewMsgs = [ v : Int, vc : Set ($viewchangeMsgs), o : Set ($preprepareMsgs), p : Int ];
pbft_typedefs == TRUE

VARIABLE
\* @type: [ request : Set ($requestMsgs), preprepare : Set ($preprepareMsgsWithRequest), prepare : Set ($prepareMsgs), commit : Set ($commitMsgs), reply : Set ($replyMsgs), checkpoint : Set ($checkpointMsgs), viewchange : Set ($viewchangeMsgs), newview : Set ($newviewMsgs) ] ;
    msgs

\* Messages each replica has accepted
VARIABLE 
\* @type: Int -> [ request : Set ($requestMsgs), preprepare : Set ($preprepareMsgs), prepare : Set ($prepareMsgs), commit : Set ($commitMsgs), reply : Set ($replyMsgs), checkpoint : Set ($checkpointMsgs), viewchange : Set ($viewchangeMsgs) ] ;
    mlogs

\* Replica views
VARIABLE
\* @type: Int -> Int;
    views

\* Service state
\* For this dummy app logic, the service state is simply the sequence number of the last request
VARIABLE 
\* @type: Int -> Int;
    states

\* Last stable checkpoint
\* Initially empty, sCheckpoint is 2f+1 checkpoint messages with the same digest and sequence number
VARIABLE
\* @type: Int -> Set ($checkpointMsgs);
    sCheckpoint

\* Flag to indicate if a view change is in progress
\* Whilst a view change is in progress, the replica will not accept any messages (other than checkpoint, view-change, and new-view messages).
VARIABLE
\* @type: Int -> Bool;
    vChange

TypeOK ==
    /\ msgs \in Messages
    /\ mlogs \in [R -> LoggedMessages]
    /\ views \in [R -> Views]
    /\ states \in [R -> States]
    /\ sCheckpoint \in [R -> SUBSET CheckpointMessages]
    /\ vChange \in [R -> BOOLEAN]

vars == <<msgs, mlogs, views, states, sCheckpoint, vChange>>

----
\* Normal case operation of PBFT

\* Castro & Liskov 4.1 "A client requests the execution of state machine operation o by sending a (REQUEST,o,t,c) message to the primary. Timestamp t is used to ensure exactly once semantics for the execution of client requests. Timestamps for c’s requests are totally ordered such that later requests have higher timestamps than earlier ones; for example, the timestamp could be the value of the client’s local clock when the request is issued. Each message sent by the replicas to the client includes the current view number, allowing the client to track the view and hence the current primary. A client sends a request to what it believes is the current primary using a point-to-point message. The primary atomically multicasts the request to all the backups using the protocol described in the next section."

\* We begin with all client requests already in the set of messages
\* We omit the operation o and client c for simplicity
Init ==
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
        viewchange |-> {}]
        ]
    /\ views = [r \in R |-> 0]
    /\ states = [r \in R |-> 0]
    /\ sCheckpoint = [r \in R |-> {}]
    /\ vChange = [r \in R |-> FALSE]

\* Castro & Liskov 4.2 "In the pre-prepare phase, the primary assigns a sequence number, n, to the request, multicasts a preprepare message with m piggybacked to all the backups, and appends the message to its log. The message has the form ((PRE-PREPARE,v,n,d),m), where v indicates the view in which the message is being sent, m is the client's request message, and d is m's digest."
\* Note that we have extended the preprepare message to include the primary's identity. This is not described in the paper as sender identity is implicit in the message signature, however, since we do not model signatures we must represent the sender explicitly. 

\* @type: Set(Int) => Int;
Max0(S) == CHOOSE x \in (S \union {0}) : \A y \in S : x >= y

\* @type: Int => Int;
NextN(i) == Max0({m.n: m \in mlogs[i].preprepare}) + 1

PrePrepare(i) ==
    /\ i = views[i] % N
    \* TODO: move to MC file
    /\ NextN(i) \in SeqNums
    /\ \E m \in (msgs.request \ mlogs[i].request) : 
        /\ msgs' = [msgs EXCEPT 
            !.preprepare = @ \cup {[
                v |-> views[i],
                p |-> i,
                n |-> NextN(i), 
                d |-> RequestDigest(m), 
                m |-> m]}]
        /\ mlogs' = [mlogs EXCEPT 
            ![i].preprepare = @ \cup {[
                v |-> views[i],
                p |-> i,
                n |-> NextN(i), 
                d |-> RequestDigest(m)]},
            ![i].request = @ \cup {m}]
        /\ UNCHANGED <<views, states, sCheckpoint, vChange>>


\* Castro & Liskov 4.2 "A backup accepts a pre-prepare message provided: 1) the signatures in the request and the pre-prepare message are correct and d is the digest for m; 2) it is in view v; 3) it has not accepted a pre-prepare message for view v and sequence number n containing a different digest; 4) the sequence number in the pre-prepare message is between a low water mark, h , and a high water mark, H. If backup accepts the ((PRE-PREPARE,v,n,d),m) message, it enters the prepare phase by multicasting a (PREPARE,v,n,d,i) message to all other replicas and adds both messages to its log. Otherwise, it does nothing."

\* @type: $preprepareMsgsWithRequest => $preprepareMsgs;
Strip(m) == [
    v |-> m.v,
    p |-> m.p,
    n |-> m.n, 
    d |-> m.d]

\* Castro & Liskov 4.3 "The low-water mark h is equal to the sequence number of the last stable checkpoint. The high water mark H = h + k, where k is big enough so that replicas do not stall waiting for a checkpoint to become stable. For example, if checkpoints are taken every 100 requests, might be 200."

\* We are using Max here but all the n's in sCheckpoint[i] are the same.
\* Alternatively, we could have used CHOOSE.
h(i) == Max0({m.n: m \in sCheckpoint[i]})

\* Watermark window size
k == 10

Prepare(i) ==
    /\ i /= views[i] % N
    /\ ~vChange[i]
    /\ \E m \in msgs.preprepare: 
        /\ m.d = RequestDigest(m.m)
        /\ m.p = m.v % N
        /\ m.v = views[i]
        /\ m.n > h(i)
        /\ m.n <= h(i) + k
        /\ \A mpp \in mlogs[i].preprepare : 
            /\ mpp.v = m.v
            /\ mpp.n = m.n
            => mpp.d = m.d 
        /\ msgs' = [msgs EXCEPT 
            !.prepare = @ \cup {[
                v |-> m.v,
                n |-> m.n, 
                i |-> i, 
                d |-> m.d]}]
        /\ mlogs' = [mlogs EXCEPT 
            ![i].request = @ \cup {m.m},
            ![i].preprepare = @ \cup {Strip(m)},
            ![i].prepare = @ \cup {[
                v |-> m.v,
                n |-> m.n, 
                i |-> i, 
                d |-> m.d]}]
    /\ UNCHANGED <<views, states, sCheckpoint, vChange>>

\* Castro & Liskov 4.2 "A replica (including the primary) accepts prepare messages and adds them to its log provided their signatures are correct, their view number equals the replica’s current view, and their sequence number is between h and H."

AcceptPrepare(i) ==
    /\ ~vChange[i]
    /\ \E m \in msgs.prepare :
        /\ m.v = views[i]
        /\ m.n > h(i)
        /\ m.n <= h(i) + k
        /\ mlogs' = [mlogs EXCEPT ![i].prepare = @ \cup {m}]
    /\ UNCHANGED <<msgs, views, states, sCheckpoint, vChange>>

\* Castro & Liskov 4.2 "We define the predicate prepared(m,v,n,i) to be true if and only if replica i has inserted in its log: the request m, a pre-prepare for m in view v with sequence number n, and 2f prepares from different backups that match the pre-prepare. The replicas verify whether the prepares match the pre-prepare by checking that they have the same view, sequence number, and digest."

Prepared(m,v,n,i) ==
    /\ m \in mlogs[i].request
    /\ \E ppm \in mlogs[i].preprepare:
        /\ ppm.v = v
        /\ ppm.d = RequestDigest(m)
        /\ ppm.n = n
    /\ Cardinality({pm \in mlogs[i].prepare: 
        pm.v = v /\ pm.d = RequestDigest(m) /\ pm.n = n}) >= 2*F

\* Castro & Liskov 4.2 "Replica multicasts a (COMMIT, v, n, D(m), i) to the other replicas when prepared becomes true. This starts the commit phase."

Commit(i) ==
    /\ ~vChange[i]
    /\ \E m \in mlogs[i].request : 
        \E n \in SeqNums :
            \E v \in Views : 
                /\ Prepared(m,v,n,i)
                /\ msgs' = [msgs EXCEPT 
                    !.commit = @ \cup {[
                        v |-> v,
                        n |-> n, 
                        i |-> i, 
                        d |-> RequestDigest(m)]}]
                /\ mlogs' = [mlogs EXCEPT 
                    ![i].commit = @ \cup {[
                        v |-> v,
                        n |-> n, 
                        i |-> i, 
                        d |-> RequestDigest(m)]}]
    /\ UNCHANGED <<views, states, sCheckpoint, vChange>>

\* Castro & Liskov 4.2 "Replicas accept commit messages and insert them in their log provided they are properly signed, the view number in the message is equal to the replica's current view, and the sequence number is between h and H."

AcceptCommit(i) ==
    /\ ~vChange[i]
    /\ \E m \in msgs.commit:
        /\ m.v = views[i]
        /\ mlogs' = [mlogs EXCEPT ![i].commit = @ \cup {m}]
    /\ UNCHANGED <<msgs, views, states, sCheckpoint, vChange>>

\* Castro & Liskov 4.2 "committed-local(m,v,n,i) is true if and only if prepared(m,v,n,i) is true and i has accepted 2f+1 commits (possibly including its own) from different replicas that match the pre-prepare for m; a commit matches a pre-prepare if they have the same view, sequence number, and digest."

CommittedLocal(m,v,n,i) ==
    /\ Prepared(m,v,n,i)
    /\ Cardinality({cm \in mlogs[i].commit: 
        cm.v = v /\ cm.d = RequestDigest(m) /\ cm.n = n}) >= 2*F + 1 

\* Castro & Liskov 4.2 "Each replica i executes the operation requested by m after committed-local(m,v,n,i) is true and i’s state reflects the sequential execution of all requests with lower sequence numbers. This ensures that all non-faulty replicas execute requests in the same order as required to provide the safety property. After executing the requested operation, replicas send a reply to the client."
\* Castro & Liskov 4.1 "A replica sends the reply to the request directly to the client. The reply has the form (REPLY,v,t,c,i,r) where v is the current view number, t is the timestamp of the corresponding request, i is the replica number, and r is the result of executing the requested operation."

\* We use dummy requests so the result is simply the request sequence number
ExecuteNoCheckpoint(i) ==
    /\ ~vChange[i]
    /\ \E m \in mlogs[i].request : 
        \E n \in SeqNums, v \in Views :
            /\ CommittedLocal(m,v,n,i)
            /\ states[i] = n - 1
            /\ n \notin Checkpoints
            /\ msgs' = [msgs EXCEPT !.reply = @ \cup {[
                v |-> v,
                t |-> m.t, 
                i |-> i, 
                r |-> n]}]
            /\ states' = [states EXCEPT ![i] = n]
    /\ UNCHANGED <<mlogs, views, sCheckpoint, vChange>>

\* Castro & Liskov 4.3 "When a replica i produces a checkpoint, it multicasts a message (CHECKPOINT,n,d,i) to the other replicas, where n is the sequence number of the last request whose execution is reflected in the state and d is the digest of the state.

\* This action is the same as ExecuteNoCheckpoint but includes sending a checkpoint message.
\* Either ExecuteNoCheckpoint or ExecuteAndCheckpoint will be enabled at point in time, not both.
ExecuteAndCheckpoint(i) ==
    /\ ~vChange[i]
    /\ \E m \in mlogs[i].request : 
        \E n \in SeqNums, v \in Views :
            /\ CommittedLocal(m,v,n,i)
            /\ states[i] = n - 1
            /\ n \in Checkpoints
            /\ msgs' = [msgs EXCEPT 
                !.reply = @ \cup {[
                    v |-> v,
                    t |-> m.t, 
                    i |-> i, 
                    r |-> n]}, 
                !.checkpoint = @ \cup {[
                    n |-> n,
                    d |-> StateDigest(n),
                    i |-> i]}]
            /\ mlogs' = [mlogs EXCEPT ![i].checkpoint = @ \cup {[
                n |-> n,
                d |-> StateDigest(n),
                i |-> i]}]
            /\ states' = [states EXCEPT ![i] = n]
    /\ UNCHANGED <<views, sCheckpoint, vChange>>

UnstableCheckpoint(i) ==
    /\ \E m \in msgs.checkpoint : 
        /\ Cardinality({mc \in mlogs[i].checkpoint : 
            mc.n = m.n /\ mc.d = m.d} \union {m}) < 2*F + 1
        /\ mlogs' = [mlogs EXCEPT 
            ![i].checkpoint = @ \cup {m}]
    /\ UNCHANGED <<msgs, views, states, sCheckpoint, vChange>>

\* Castro & Liskov 4.3 "Each replica collects checkpoint messages in its log until it has 2f+1 of them for sequence number n with the same digest d signed by different replicas (including possibly its own such message). These 2f+1 messages are the proof of correctness for the checkpoint."

StableCheckpoint(i) ==
    /\ \E m \in msgs.checkpoint : 
        /\ Cardinality({mc \in mlogs[i].checkpoint : 
            mc.n = m.n /\ mc.d = m.d} \union {m}) = 2*F + 1
        /\ mlogs' = [mlogs EXCEPT 
            ![i].preprepare = {mpp \in @ : mpp.n > m.n},
            ![i].prepare = {mp \in @ : mp.n > m.n},
            ![i].commit = {mc \in @ : mc.n > m.n},
            ![i].checkpoint = {mc \in @ : mc.n > m.n}]
        /\ sCheckpoint' = [sCheckpoint EXCEPT ![i] = {mc \in mlogs[i].checkpoint : mc.n = m.n /\ mc.d = m.d} \union {m}]
    /\ UNCHANGED <<msgs, views, states, vChange>>

\* Castro & Liskov 4.4 "If the timer of backup i expires in view v, the backup starts a view change to move the system to view v+1. It stops accepting messages (other than checkpoint, view-change, and new-view messages) and multicasts a (VIEW-CHANGE,v+1,n,C,P,i) message to all replicas. Here n is the sequence number of the last stable checkpoint s known to i, C is a set of 2f+1 valid checkpoint messages proving the correctness of s, and P is a set containing a set P_m for each request m that prepared at i with a sequence number higher than n. Each set P_m contains a valid pre-prepare message (without the corresponding client message) and 2f matching, valid prepare messages signed by different backups with the same view, sequence number, and the digest of m.

\* Set of requests with views and sequence numbers prepared at replica i with sequence numbers higher than n
PreparedAfterN(i,n) == 
    {<<m, v, nm>> \in (mlogs[i].request \X Views \X SeqNums) 
        : nm > n /\ Prepared(m,v,nm,i)}

\* Produce a proof that a request m was prepared at replica i with sequence number n and view v
Pm(m, v, n, i) == [
    preprepare |-> CHOOSE ppm \in mlogs[i].preprepare: 
        ppm.v = v /\ ppm.n = n /\ ppm.d = RequestDigest(m),
    \* TODO: this is not guaranteed to contain exactly 2f matching prepare messages, there might be more
    prepare |-> {pm \in mlogs[i].prepare:
        pm.v = v /\ pm.n = n /\ pm.d = RequestDigest(m)}]

GenerateViewChangeMsg(i) ==
    LET n == Max0({m.n: m \in sCheckpoint[i]}) 
    IN [v |-> views[i] + 1,
        n |-> n,
        c |-> sCheckpoint[i],
        p |-> {Pm(m, v, nm, i) : <<m, v, nm>> \in PreparedAfterN(i, n)},
        i |-> i]

\* This specification does not model timers, so view changes are always enabled for all backups.      
ViewChange(i) ==
    /\ i /= views[i] % N
    \* TODO: Move this to MC
    /\ views[i] \in Views
    /\ vChange' = [vChange EXCEPT ![i] = TRUE]
    /\ msgs' = [msgs EXCEPT 
        !.viewchange = @ \cup {GenerateViewChangeMsg(i)}]
    /\ UNCHANGED <<mlogs, views, states, sCheckpoint>>

\* True iff cp is a valid checkpoint proof for sequence number n.
ValidCheckpointProof(cp, n) ==
    \/ /\ n = 0
       /\ cp = {}
    \/ /\ n /= 0
       /\ Cardinality(cp) = 2*F + 1
       /\ \E d \in StateDigests: 
            \A m \in cp:
                /\ m.n = n
                /\ m.d = StateDigest(n)

\* True iff pp is a valid prepare proof for a sequence number after n_min.
ValidPrepareProof(pp, n_min) ==
    \E v \in Views, n \in SeqNums, d \in RequestDigests:
        /\ n > n_min
        /\ pp.preprepare.v = v
        /\ pp.preprepare.p = v % N
        /\ pp.preprepare.n = n
        /\ pp.preprepare.d = d
        /\ Cardinality(pp.prepare) = 2*F
        /\ \A ppm \in pp.prepare:
            /\ ppm.v = v
            /\ ppm.n = n
            /\ ppm.d = d

\* The next primary accepts valid view-changes messages. The seperate NewView action is used to act on them.
AcceptViewChange(i) ==
    \* check that replica i will be next primary
    /\ i = (views[i] + 1) % N
    /\ \E m \in msgs.viewchange : 
        /\ m.v = views[i] + 1
        /\ ValidCheckpointProof(m.c, m.n)
        /\ \A pp \in m.p: ValidPrepareProof(pp, m.n)
        /\ mlogs' = [mlogs EXCEPT ![i].viewchange = @ \cup {m}]
    /\ UNCHANGED <<msgs, views, states, sCheckpoint, vChange>>

\* Castro & Liskov 4.4 "When the primary p of view v+1 receives 2f valid view-change messages for view v+1 from other replicas, it multicasts a (NEW-VIEW,v+1,V,O) message to all other replicas, where V is a set containing the valid view-change messages received by the primary plus the view-change message for v+1 the primary sent (or would have sent), and is a set of pre-prepare messages (without the piggybacked request)." 

NewView(i) ==
    \* check that replica i will be next primary
    /\ i = (views[i] + 1) % N
    \* check for 2f view-change messages
    \* we need not confirm that the view-change messages are valid as this is done in AcceptViewChange
    /\ Cardinality({m \in mlogs[i].viewchange : m.v = views[i] + 1}) = 2*F
    \* TODO calc O
    /\ msgs' = [msgs EXCEPT !.newview = @ \cup {[
        v |-> views[i] + 1,
        vc |-> {m \in mlogs[i].viewchange : m.v = views[i] + 1} \cup {GenerateViewChangeMsg(i)},
        o |-> {},
        p |-> i]}]
    /\ views' = [views EXCEPT ![i] = views[i] + 1]
    /\ vChange' = [vChange EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<mlogs, states, sCheckpoint>>

AcceptNewView(i) ==
    \* TODO
    UNCHANGED <<msgs, mlogs, views, states, sCheckpoint, vChange>>

Next ==
    \E i \in R : 
        \/ PrePrepare(i)
        \/ Prepare(i)
        \/ AcceptPrepare(i)
        \/ Commit(i)
        \/ AcceptCommit(i)
        \/ ExecuteNoCheckpoint(i)
        \/ ExecuteAndCheckpoint(i)
        \/ UnstableCheckpoint(i)
        \/ StableCheckpoint(i)
        \/ ViewChange(i)
        \/ AcceptViewChange(i)
        \/ NewView(i)
        \/ AcceptNewView(i)

Spec == Init /\ [][Next]_vars

\* Castro & Liskov 4.1 "The client waits for f+1 replies with valid signatures from different replicas, and with the same t and r, before accepting the result r"

Decided(t,r) == 
    Cardinality({m \in msgs.reply: m.t = t /\ m.r = r}) >= F+1

OneReplyInv == 
    \A t \in Tstamps :
        \A r1, r2 \in Results :
            Decided(t,r1) /\ Decided(t,r2) => r1 = r2

OneResultInv == 
    \A t1, t2 \in Tstamps :
        \A r \in Results :
            Decided(t1,r) /\ Decided(t2,r) => t1 = t2

\* SafetyInv specifies that there's a 1:1 correspondence between request timestamps and results (sequence numbers)
SafetyInv == OneReplyInv /\ OneResultInv

\*  Castro & Liskov 4.2 "committed(m,v,n) is true if and only if prepared(m,v,n,i) is true for all i in some set of f+1 non-faulty replicas"

Committed(m,v,n) ==
    Cardinality({i \in (R \ ByzR) : Prepared(m,v,n,i)}) >= F+1

\*  Castro & Liskov 4.2 "The commit phase ensures the following invariant: if committed-local(m,v,n,i) is true for some non-faulty i then committed(m,v,n) is true. This invariant and the view-change protocol described inSection 4.4 ensure that non-faulty replicas agree on the sequence numbers of requests that commit locally even if they commit in different views at each replica. Furthermore, it ensures that any request that commits locally at a non-faulty replica will commit at f+1 or more non-faulty replicas eventually."

CommittedInv ==
    \A m \in RequestMessages, v \in Views, n \in SeqNums, i \in (R \ ByzR): CommittedLocal(m,v,n,i) => Committed(m,v,n)

----
\* A variant of spec for modeling byzantine behavior

InjectPreprepare(i) ==
    /\ \E m \in PrePrepareWithRequestMessages : 
        /\ m.p = i
        \* A byzantine replica can produce messages with invalid digests but we do not model that here to reduce state space as replicas will reject such messages
        /\ m.d = RequestDigest(m.m)
        \* Similarly, we do not model non-primary replicas sending preprepares
        /\ m.p = m.v % N
        /\ msgs' = [msgs EXCEPT !.preprepare = @ \cup {m}]
    /\ UNCHANGED <<mlogs, views, states, sCheckpoint, vChange>>

InjectPrepare(i) ==
    /\ \E m \in PrepareMessages : 
        /\ m.i = i
        /\ msgs' = [msgs EXCEPT !.prepare = @ \cup {m}]
    /\ UNCHANGED <<mlogs, views, states, sCheckpoint, vChange>>

InjectCommit(i) ==
    /\ \E m \in CommitMessages : 
        /\ m.i = i
        /\ msgs' = [msgs EXCEPT !.commit = @ \cup {m}]
    /\ UNCHANGED <<mlogs, views, states, sCheckpoint, vChange>>

InjectReply(i) ==
    /\ \E m \in ReplyMessages : 
        /\ m.i = i
        /\ msgs' = [msgs EXCEPT !.reply = @ \cup {m}]
    /\ UNCHANGED <<mlogs, views, states, sCheckpoint, vChange>>

InjectCheckpoint(i) ==
    /\ \E m \in CheckpointMessages : 
        /\ m.i = i
        /\ msgs' = [msgs EXCEPT !.checkpoint = @ \cup {m}]
    /\ UNCHANGED <<mlogs, views, states, sCheckpoint, vChange>> 

\* Any message sent by a Byzantine replica can be injected into the system
InjectMessage ==
    \E i \in ByzR : 
        \/ InjectPreprepare(i)
        \/ InjectPrepare(i)
        \/ InjectCommit(i)
        \/ InjectReply(i)
        \/ InjectCheckpoint(i)

\* Extends Next to allow 
NextByz ==
    \/ Next
    \/ InjectMessage

SpecByz == Init /\ [][NextByz]_vars

----

\* This is the beginning of a inductive invariant for Safety. However, the state space is too large to use this as an initial state with TLC or Apalache.
Inv == 
    /\ TypeOK
    /\ SafetyInv

SpecInv == Inv /\ [][Next]_vars

----
\* Invariants for debugging, add to cfg to enable

DecidedTstamps == {t \in Tstamps: \E r \in Results: Decided(t,r)}

AtLeastOneDecidedDebugInv == DecidedTstamps = {}

AtLeastTwoDecidedDebugInv == Cardinality(DecidedTstamps) < 2

AllDecidedDebugInv == DecidedTstamps /= Tstamps

AnyRepliesDebugInv ==
    msgs.reply # {}

NoCheckpointsDebugInv ==
    msgs.checkpoint = {}

----

====