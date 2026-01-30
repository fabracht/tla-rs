---- MODULE MQDBQuorum ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, RequiredAcks

VARIABLES acked, failed, stale_seen, result

vars == <<acked, failed, stale_seen, result>>

Init ==
    /\ acked = {}
    /\ failed = {}
    /\ stale_seen = FALSE
    /\ result = "pending"

ComputeResult(a, f, ss) ==
    IF Cardinality(a) >= RequiredAcks
    THEN "success"
    ELSE IF ss
    THEN "failed"
    ELSE LET remaining == Cardinality(Nodes) - Cardinality(a) - Cardinality(f)
             possible == Cardinality(a) + remaining
         IN IF possible < RequiredAcks
            THEN "failed"
            ELSE "pending"

AckOk(node) ==
    /\ result = "pending"
    /\ node \in Nodes
    /\ node \notin acked
    /\ node \notin failed
    /\ LET new_acked == acked \cup {node}
       IN /\ acked' = new_acked
          /\ result' = ComputeResult(new_acked, failed, stale_seen)
    /\ UNCHANGED <<failed, stale_seen>>

AckStale(node) ==
    /\ result = "pending"
    /\ node \in Nodes
    /\ node \notin acked
    /\ node \notin failed
    /\ stale_seen' = TRUE
    /\ failed' = failed \cup {node}
    /\ result' = "failed"
    /\ UNCHANGED acked

NodeTimeout(node) ==
    /\ result = "pending"
    /\ node \in Nodes
    /\ node \notin acked
    /\ node \notin failed
    /\ LET new_failed == failed \cup {node}
       IN /\ failed' = new_failed
          /\ result' = ComputeResult(acked, new_failed, stale_seen)
    /\ UNCHANGED <<acked, stale_seen>>

Next ==
    \/ \E n \in Nodes : AckOk(n)
    \/ \E n \in Nodes : AckStale(n)
    \/ \E n \in Nodes : NodeTimeout(n)

InvAckedDisjointFailed ==
    acked \cap failed = {}

InvStaleImpliesFailed ==
    stale_seen => result = "failed"

InvQuorumImpliesSuccess ==
    Cardinality(acked) >= RequiredAcks => result = "success"

InvImpossibleQuorumImpliesFailed ==
    LET remaining == Cardinality(Nodes) - Cardinality(acked) - Cardinality(failed)
        possible == Cardinality(acked) + remaining
    IN (possible < RequiredAcks /\ ~stale_seen) => result = "failed"

====
