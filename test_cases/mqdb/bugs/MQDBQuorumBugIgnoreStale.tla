---- MODULE MQDBQuorumBugIgnoreStale ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, RequiredAcks

VARIABLES acked, failed, stale_seen, result

vars == <<acked, failed, stale_seen, result>>

Init ==
    /\ acked = {}
    /\ failed = {}
    /\ stale_seen = FALSE
    /\ result = "pending"

ComputeResultBuggy(a, f, ss) ==
    IF Cardinality(a) >= RequiredAcks
    THEN "success"
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
          /\ result' = ComputeResultBuggy(new_acked, failed, stale_seen)
    /\ UNCHANGED <<failed, stale_seen>>

AckStaleBuggy(node) ==
    /\ result = "pending"
    /\ node \in Nodes
    /\ node \notin acked
    /\ node \notin failed
    /\ stale_seen' = TRUE
    /\ failed' = failed \cup {node}
    /\ result' = ComputeResultBuggy(acked, failed \cup {node}, TRUE)
    /\ UNCHANGED acked

NodeTimeout(node) ==
    /\ result = "pending"
    /\ node \in Nodes
    /\ node \notin acked
    /\ node \notin failed
    /\ LET new_failed == failed \cup {node}
       IN /\ failed' = new_failed
          /\ result' = ComputeResultBuggy(acked, new_failed, stale_seen)
    /\ UNCHANGED <<acked, stale_seen>>

Next ==
    \/ \E n \in Nodes : AckOk(n)
    \/ \E n \in Nodes : AckStaleBuggy(n)
    \/ \E n \in Nodes : NodeTimeout(n)

InvStaleImpliesFailed ==
    stale_seen => result = "failed"

====
