---- MODULE pbft ----
\* This TLA+ specification describes the normal case operation of Practical Byzantine Fault Tolerance protocol.
\* See https://www.pmg.csail.mit.edu/papers/osdi99.pdf for a full description of the protocol.

\* This specification can be checked with TLC and Apalache (https://apalache.informal.systems/). Note that typechecking with Apalache requires the --features=no-rows flag.

EXTENDS Integers, FiniteSets, TLC

\* This iteration of the specification is significantly simplified from the original paper.
\* We make the following simplifying assumptions:
\* - Always 4 nodes
\* - no view changes, 1 fixed primary (node R1) 
\* - no byzantine primaries
\* - no liveness properties
\* - dummy requests
\* - one client with concurrent requests
\* - no garbage collection/checkpointing (Sec. 4.3)

\* Set of replicas
\* Castro & Liskov 4 "We denote the set of replicas by R and identify each replica using an integer in {0,..|R|-1}."
CONSTANT 
\* @type: Set(Str)    
    R

N == Cardinality(R)
F == (N - 1) \div 3

\* Castro & Liskov 4 "For simplicity, we assume N=3F+1 where F is the maximum number of replicas that may be faulty."
ASSUME N = 3*F + 1

\* A fixed primary
CONSTANT 
\* @type: Str
    PRIMARY
ASSUME PRIMARY \in R

\* Don't include the primary in the symmetry set
Symmetry == Permutations(R \ {PRIMARY})

\* Byzantine replicas (backups only)
CONSTANT
\* @type: Set(Str)    
    ByzR
ASSUME ByzR \subseteq R

\* Set of all request timestamps
\* We use just natural numbers as there's a single client
Tstamps == 1..2

\* Bounding sequence numbers to the total number of requests
SeqNums == Tstamps

\* Our dummy app will return the request sequence number
Results == SeqNums

Views == {0}

\* Digest takes a client request and returns a unique identifier
\* Since we are assuming timestamps are unique, we can use them as the digest
\* @type: [ t : Int ] => Int;
Digest(m) == m.t

Digests == Tstamps

RequestMessages == 
    [t : Tstamps]

PrePrepareWithRequestMessages == 
    [v: Views, n : SeqNums, d : Digests, m : RequestMessages]

PrePrepareMessages == 
    [v: Views, n : SeqNums, d : Digests]

PrepareMessages == 
    [v : Views, i : R, n : SeqNums, d : Digests]

CommitMessages ==
    [v : Views, i : R, n : SeqNums, d : Digests]

ReplyMessages ==
    [v : Views, i : R, t : Tstamps, r: Results]

Messages == [ 
    request : SUBSET RequestMessages, 
    preprepare : SUBSET PrePrepareWithRequestMessages,
    prepare : SUBSET PrepareMessages,
    commit : SUBSET CommitMessages,
    reply : SUBSET ReplyMessages]

LoggedMessages == [
    request : SUBSET RequestMessages, 
    preprepare : SUBSET PrePrepareMessages,
    prepare : SUBSET PrepareMessages,
    commit : SUBSET CommitMessages,
    reply : SUBSET ReplyMessages]

\* Set of messages ever sent
VARIABLE
\* @type: [ request : Set ([ t : Int ]), preprepare : Set ([ v : Int, n : Int, d : Int,  m : [ t : Int ] ]), prepare : Set ([ v : Int, i : Str, n : Int, d : Int ]), commit : Set ([ v : Int, i : Str, n : Int, d : Int ]), reply : Set ([ v : Int, i : Str, t : Int, r : Int ]) ];
    msgs

\* Messages each replica has accepted
VARIABLE 
\* @type: Str -> [ request : Set ([ t : Int ]), preprepare : Set ([ v : Int, n : Int, d : Int,  m : [ t : Int ] ]), prepare : Set ([ v : Int, i : Str, n : Int, d : Int ]), commit : Set ([ v : Int, i : Str, n : Int, d : Int ]), reply : Set ([ v : Int, i : Str, t : Int, r : Int ]) ];
    mlogs

\* Replica views
VARIABLE
\* @type: Str -> Int;
    views

TypeOK ==
    /\ msgs \in Messages
    /\ mlogs \in [R -> LoggedMessages]
    /\ views \in [R -> Views]

vars == <<msgs, mlogs, views>>

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
        reply |-> {}]
    /\ mlogs = [r \in R |-> [
        request |-> {},
        preprepare |-> {},
        prepare |-> {},
        commit |-> {},
        reply |-> {}]
        ]
    /\ views = [r \in R |-> 0]

\* Castro & Liskov 4.2 "In the pre-prepare phase, the primary assigns a sequence number, n, to the request, multicasts a preprepare message with m piggybacked to all the backups, and appends the message to its log. The message has the form ((PRE-PREPARE,v,n,d),m), where v indicates the view in which the message is being sent, m is the client's request message, and d is m's digest."

\* @type: Set(Int) => Int;
Max0(S) == CHOOSE x \in (S \union {0}) : \A y \in S : x >= y

\* @type: Str => Int;
NextN(i) == Max0({m.n: m \in mlogs[i].preprepare}) + 1

PrePrepare(i) ==
    /\ i = PRIMARY
    /\ \E m \in (msgs.request \ mlogs[i].request) : 
        /\ msgs' = [msgs EXCEPT 
            !.preprepare = @ \cup {[
                v |-> views[i],
                n |-> NextN(i), 
                d |-> Digest(m), 
                m |-> m]}]
        /\ mlogs' = [mlogs EXCEPT 
            ![i].preprepare = @ \cup {[
                v |-> views[i],
                n |-> NextN(i), 
                d |-> Digest(m)]},
            ![i].request = @ \cup {m}]
        /\ UNCHANGED views


\* Castro & Liskov 4.2 "A backup accepts a pre-prepare message provided: 1) the signatures in the request and the pre-prepare message are correct and d is the digest for m; 2) it is in view v; 3) it has not accepted a pre-prepare message for view v and sequence number n containing a different digest; 4) the sequence number in the pre-prepare message is between a low water mark, h , and a high water mark, H. If backup accepts the ((PRE-PREPARE,v,n,d),m) message, it enters the prepare phase by multicasting a (PREPARE,v,n,d,i) message to all other replicas and adds both messages to its log. Otherwise, it does nothing."

\* @type: [ n : Int, d : Int,  m : [ t : Int ] ] => [ n : Int, d : Int ];
Strip(m) == [
    v |-> m.v,
    n |-> m.n, 
    d |-> m.d]

Prepare(i) ==
    /\ i /= PRIMARY
    /\ \E m \in msgs.preprepare: 
        /\ m.d = Digest(m.m)
        /\ m.v = views[i]
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
    /\ UNCHANGED views

\* Castro & Liskov 4.2 "A replica (including the primary) accepts prepare messages and adds them to its log provided their signatures are correct, their view number equals the replica’s current view, and their sequence number is between h and H."

AcceptPrepare(i) ==
    /\ \E m \in msgs.prepare :
        /\ m.v = views[i]
        /\ mlogs' = [mlogs EXCEPT ![i].prepare = @ \cup {m}]
    /\ UNCHANGED <<msgs, views>>

\* Castro & Liskov 4.2 "We define the predicate prepared(m,v,n,i) to be true if and only if replica i has inserted in its log: the request m, a pre-prepare for m in view v with sequence number n, and 2f prepares from different backups that match the pre-prepare. The replicas verify whether the prepares match the pre-prepare by checking that they have the same view, sequence number, and digest."

Prepared(m,v,n,i) ==
    /\ m \in mlogs[i].request
    /\ \E ppm \in mlogs[i].preprepare:
        /\ ppm.v = v
        /\ ppm.d = Digest(m)
        /\ ppm.n = n
    /\ Cardinality({pm \in mlogs[i].prepare: 
        pm.v = v /\ pm.d = Digest(m) /\ pm.n = n}) >= 2*F

\* Castro & Liskov 4.2 "Replica multicasts a (COMMIT, v, n, D(m), i) to the other replicas when prepared becomes true. This starts the commit phase."

Commit(i) ==
    /\ \E m \in mlogs[i].request : 
        \E n \in SeqNums :
            \E v \in Views : 
                /\ Prepared(m,v,n,i)
                /\ msgs' = [msgs EXCEPT 
                    !.commit = @ \cup {[
                        v |-> v,
                        n |-> n, 
                        i |-> i, 
                        d |-> Digest(m)]}]
                /\ mlogs' = [mlogs EXCEPT 
                    ![i].commit = @ \cup {[
                        v |-> v,
                        n |-> n, 
                        i |-> i, 
                        d |-> Digest(m)]}]
    /\ UNCHANGED views

\* Castro & Liskov 4.2 "Replicas accept commit messages and insert them in their log provided they are properly signed, the view number in the message is equal to the replica's current view, and the sequence number is between h and H."

AcceptCommit(i) ==
    /\ \E m \in msgs.commit:
        /\ m.v = views[i]
        /\ mlogs' = [mlogs EXCEPT ![i].commit = @ \cup {m}]
    /\ UNCHANGED <<msgs, views>>

\* Castro & Liskov 4.2 "committed-local(m,v,n,i) is true if and only if prepared(m,v,n,i) is true and i has accepted 2f+1 commits (possibly including its own) from different replicas that match the pre-prepare for m; a commit matches a pre-prepare if they have the same view, sequence number, and digest."

CommittedLocal(m,v,n,i) ==
    /\ Prepared(m,v,n,i)
    /\ Cardinality({cm \in mlogs[i].commit: 
        cm.v = v /\ cm.d = Digest(m) /\ cm.n = n}) >= 2*F + 1 

\* Castro & Liskov 4.2 "Each replica i executes the operation requested by m after committed-local(m,v,n,i) is true and i’s state reflects the sequential execution of all requests with lower sequence numbers. This ensures that all non-faulty replicas execute requests in the same order as required to provide the safety property. After executing the requested operation, replicas send a reply to the client."
\* Castro & Liskov 4.1 "A replica sends the reply to the request directly to the client. The reply has the form (REPLY,v,t,c,i,r) where v is the current view number, t is the timestamp of the corresponding request, i is the replica number, and r is the result of executing the requested operation."

\* We use dummy requests so the result is simply the request sequence number
Reply(i) ==
    /\ \E m \in mlogs[i].request : 
            \E n \in SeqNums :
                \E v \in Views :
                    /\ CommittedLocal(m,v,n,i)
                    /\ msgs' = [msgs EXCEPT !.reply = @ \cup {[
                        v |-> v,
                        t |-> m.t, 
                        i |-> i, 
                        r |-> n]}]
    /\ UNCHANGED <<mlogs, views>>

Next ==
    \/ \E i \in R : 
        \/ PrePrepare(i)
        \/ Prepare(i)
        \/ AcceptPrepare(i)
        \/ Commit(i)
        \/ AcceptCommit(i)
        \/ Reply(i)

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


Inv == 
    /\ TypeOK
    /\ SafetyInv
    /\ Init

SpecInv == Inv /\ [][Next]_vars

----
\* Invariants for debugging, add to cfg to enable

DecidedDebugInv == ~Decided(1,1)

AnyRepliesDebugInv ==
    msgs.preprepare # {}

----
\* A variant of spec for modeling byzantine behavior

\* Any message sent by a Byzantine backup can be injected into the system
InjectBackupMessage ==
    /\ \E i \in ByzR : 
        \/ \E m \in PrepareMessages : 
            /\ m.i = i
            /\ msgs' = [msgs EXCEPT !.prepare = @ \cup {m}]
        \/ \E m \in CommitMessages :
            /\ m.i = i
            /\ msgs' = [msgs EXCEPT !.commit = @ \cup {m}]
        \/ \E m \in ReplyMessages :
            /\ m.i = i
            /\ msgs' = [msgs EXCEPT !.reply = @ \cup {m}]
    /\ UNCHANGED <<mlogs, views>>

\* Extends Next to allow 
NextByz ==
    \/ Next
    \/ InjectBackupMessage

SpecByz == Init /\ [][NextByz]_vars

====