---- MODULE MQDBCore_BugDoubleCreate ----
(* BUG: Create allowed on existing record (missing existence check)
   This violates InvNoOverwrite *)
EXTENDS Naturals, FiniteSets

CONSTANTS Ids, Values, MaxRetries, MaxSeq

VARIABLES store, outbox, dead_letter, event_seq

Init ==
    /\ store = [i \in Ids |-> "nil"]
    /\ outbox = {}
    /\ dead_letter = {}
    /\ event_seq = 0

(* BUG: Missing "store[id] = nil" check - allows overwriting existing data *)
Create(id, data) ==
    /\ event_seq < MaxSeq
    (* /\ store[id] = "nil"  <- MISSING! *)
    /\ data # "nil"
    /\ store' = [store EXCEPT ![id] = data]
    /\ event_seq' = event_seq + 1
    /\ outbox' = outbox \cup {[seq |-> event_seq, op |-> "create", retries |-> 0]}
    /\ UNCHANGED dead_letter

Delete(id) ==
    /\ event_seq < MaxSeq
    /\ store[id] # "nil"
    /\ store' = [store EXCEPT ![id] = "nil"]
    /\ event_seq' = event_seq + 1
    /\ outbox' = outbox \cup {[seq |-> event_seq, op |-> "delete", retries |-> 0]}
    /\ UNCHANGED dead_letter

DeliverEvent(entry) ==
    /\ entry \in outbox
    /\ outbox' = outbox \ {entry}
    /\ UNCHANGED <<store, dead_letter, event_seq>>

Next ==
    \/ \E i \in Ids, v \in Values : Create(i, v)
    \/ \E i \in Ids : Delete(i)
    \/ \E entry \in outbox : DeliverEvent(entry)

(* Store should not have data overwritten - create events should have seq 0 only once *)
InvNoOverwrite ==
    Cardinality({e \in outbox : e.op = "create"}) <= 1

====
