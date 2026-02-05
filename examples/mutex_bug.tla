---- MODULE mutex_bug ----
EXTENDS Naturals

CONSTANT Procs

VARIABLES pc, lock

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ lock = "free"

Acquire(p) ==
    /\ pc[p] = "idle"
    /\ lock' = p
    /\ pc' = [pc EXCEPT ![p] = "critical"]

Release(p) ==
    /\ pc[p] = "critical"
    /\ lock' = "free"
    /\ pc' = [pc EXCEPT ![p] = "idle"]

Next ==
    \E p \in Procs:
        \/ Acquire(p)
        \/ Release(p)

TypeOK ==
    /\ pc \in [Procs -> {"idle", "critical"}]
    /\ lock \in Procs \cup {"free"}

InvMutualExclusion ==
    \A p1, p2 \in Procs:
        (pc[p1] = "critical" /\ pc[p2] = "critical") => p1 = p2

====
