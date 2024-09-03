

$ bin/apalache-mc check --config=APApbft.cfg --no-deadlock APApbft.tla

---- MODULE APApbft ----
\* PBFT model for checking with Apalache

EXTENDS pbft, Apalache

\* Set of replicas
MC_R == 0..3

\* Set of requests which are byzantine
\* @type: Set(Int);
MC_ByzR == MC_R

MC_Tstamps == 1..3

MC_Views == 0..2

\* @type: Set(Int);
MC_Checkpoints == {2}

-------------------------

MsgsConstraintEmpty ==
    /\ msgs = [ 
        request |-> [t : Tstamps],
        preprepare |-> {},
        prepare |-> {},
        commit |-> {},
        reply |-> {},
        checkpoint |-> {},
        viewchange |-> {},
        newview |-> {}]

MsgsConstraint ==
    /\ \A r \in msgs.request :
        /\ r.t \in Tstamps
    /\ \A pp \in msgs.preprepare :
        /\ pp.v \in Views
        /\ pp.p \in R
        /\ pp.n \in SeqNums
        /\ pp.d \in RequestDigests
    /\ \A p \in msgs.prepare :
        /\ p.v \in Views
        /\ p.i \in R
        /\ p.n \in SeqNums
        /\ p.d \in RequestDigests
    /\ \A c \in msgs.commit :
        /\ c.v \in Views
        /\ c.i \in R
        /\ c.n \in SeqNums
        /\ c.d \in RequestDigests
    /\ \A r \in msgs.reply :
        /\ r.v \in Views
        /\ r.i \in R
        /\ r.t \in Tstamps
        /\ r.r \in Results
    /\ \A c \in msgs.checkpoint :
        /\ c.n \in SeqNums
        /\ c.d \in StateDigests
        /\ c.i \in R
    /\ \A v \in msgs.viewchange :
        /\ v.v \in Views
        /\ v.i \in R
        /\ v.n \in SeqNums \union {0}
        /\ \A c \in v.c : \* SUBSET CheckpointMessages
            /\ c.n \in SeqNums
            /\ c.d \in StateDigests
            /\ c.i \in R
        /\ \A p \in v.p : \* SUBSET PrepareProof
                /\ p.preprepare.v \in Views
                /\ p.preprepare.p \in R
                /\ p.preprepare.n \in SeqNums
                /\ p.preprepare.d \in RequestDigests
                /\ \A p1 \in p.prepare : \* SUBSET PrepareMessages
                    /\ p1.v \in Views
                    /\ p1.i \in R
                    /\ p1.n \in SeqNums
                    /\ p1.d \in RequestDigests
    /\ \A n \in msgs.newview :
        /\ n.v \in Views
        /\ n.p \in R
        /\ \A v \in n.vc : \* SUBSET ViewChangeMessages
            /\ v.v \in Views
            /\ v.i \in R
            /\ v.n \in SeqNums
            /\ \A c \in v.c : \* SUBSET CheckpointMessages
                /\ c.n \in SeqNums
                /\ c.d \in StateDigests
                /\ c.i \in R
            /\ \A p \in v.p : \* SUBSET PrepareProof
                /\ p.preprepare.v \in Views
                /\ p.preprepare.p \in R
                /\ p.preprepare.n \in SeqNums
                /\ p.preprepare.d \in RequestDigests
                /\ \A p1 \in p.prepare : \* SUBSET PrepareMessages
                    /\ p1.v \in Views
                    /\ p1.i \in R
                    /\ p1.n \in SeqNums
                    /\ p1.d \in RequestDigests
        /\ \A pp \in n.o : \* SUBEST PrePrepareMessages
            /\ pp.v \in Views
            /\ pp.p \in R
            /\ pp.n \in SeqNums
            /\ pp.d \in RequestDigests    

\* THEOREM msgs \in Messages => MsgsConstraint
\* BY DEF Messages, MsgsConstraint, NewViewMessages, PrepareProof, PrepareMessages, ViewChangeMessages, CheckpointMessages, PrePrepareMessages, CommitMessages, ReplyMessages, RequestMessages

MlogsConstraintEmpty ==
    /\ mlogs = [r \in R |-> [
        request |-> {},
        preprepare |-> {},
        prepare |-> {},
        commit |-> {},
        reply |-> {},
        checkpoint |-> {},
        viewchange |-> {}]
        ]

MlogsConstraint ==
    \* mlogs is defined for all replicas (outside of TLA+, one would call it a total function). Without this constraint, 
    \* Apalache!Gen may generate a function that is not defined for all replicas.
    /\ DOMAIN mlogs = R  
    /\ \A rr \in DOMAIN mlogs :
        /\ \A r \in mlogs[rr].request :
            /\ r.t \in Tstamps
        /\ \A pp \in mlogs[rr].preprepare :
            /\ pp.v \in Views
            /\ pp.p \in R
            /\ pp.n \in SeqNums
            /\ pp.d \in RequestDigests
        /\ \A p \in mlogs[rr].prepare :
            /\ p.v \in Views
            /\ p.i \in R
            /\ p.n \in SeqNums
            /\ p.d \in RequestDigests
        /\ \A c \in mlogs[rr].commit :
            /\ c.v \in Views
            /\ c.i \in R
            /\ c.n \in SeqNums
            /\ c.d \in RequestDigests
        /\ \A r \in mlogs[rr].reply :
            /\ r.v \in Views
            /\ r.i \in R
            /\ r.t \in Tstamps
            /\ r.r \in Results
        /\ \A c \in mlogs[rr].checkpoint :
            /\ c.n \in SeqNums
            /\ c.d \in StateDigests
            /\ c.i \in R
        /\ \A v \in mlogs[rr].viewchange :
            /\ v.v \in Views
            /\ v.i \in R
            /\ v.n \in SeqNums \union {0}
            /\ \A c \in v.c : \* SUBSET CheckpointMessages
                /\ c.n \in SeqNums
                /\ c.d \in StateDigests
                /\ c.i \in R
            /\ \A p \in v.p : \* SUBSET PrepareProof
                    /\ p.preprepare.v \in Views
                    /\ p.preprepare.p \in R
                    /\ p.preprepare.n \in SeqNums
                    /\ p.preprepare.d \in RequestDigests
                    /\ \A p1 \in p.prepare : \* SUBSET PrepareMessages
                        /\ p1.v \in Views
                        /\ p1.i \in R
                        /\ p1.n \in SeqNums
                        /\ p1.d \in RequestDigests

GenInit ==
    /\ msgs = Gen(5)
    /\ mlogs = Gen(5)
    /\ views = Gen(10)
    /\ states = Gen(10)
    /\ sCheckpoint = Gen(10)
    /\ vChange = Gen(10)

    \* Apalache's documentation advises to conjoin TypeOK to GenInit to further constraint
    \* the values generated by Gen.  This is necessary because Gen generates values that
    \* satisfy Apalache's type system, but not necessarily the spec's TypeOK predicate.
    \* /\ TypeOK
    \* Unfortunately, Apalache explodes when it encounters the spec's TypeOK predicate 
    \* because of multiple levels of nested subsets.  Therefore, we inline and partially
    \* rewrite the definition of TypeOK into the following abomination.
    /\ MsgsConstraint
    /\ MlogsConstraint
    \* TypeOK!3 to TypeOK!6 are inlined from the original TypeOK predicate
    \* (! not supported by Apalache).
    /\ views \in [R -> Views]
    /\ states \in [R -> States]
    /\ sCheckpoint \in [R -> SUBSET CheckpointMessages]
    /\ vChange \in [R -> BOOLEAN]

    /\ SafetyInv
    \* /\ CommittedInv  \* Conjoining CommittedInv to GenInit causes a huge slowdown in Apalache.
    \* /\ Inv    \* Inv is defined in terms of TypeOK and, thus, cannot be used in combination with Gen.

====