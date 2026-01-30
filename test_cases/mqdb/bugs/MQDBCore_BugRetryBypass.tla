---- MODULE MQDBCore_BugRetryBypass ----
(* BUG: Retry allowed even when retries >= MaxRetries
   This should violate InvRetryBounded *)
EXTENDS Naturals, FiniteSets

CONSTANTS Ids, Values, MaxRetries, MaxSeq

VARIABLES store, outbox, dead_letter, event_seq

Init ==
    /\ store = [i \in Ids |-> "nil"]
    /\ outbox = {}
    /\ dead_letter = {}
    /\ event_seq = 0

Create(id, data) ==
    /\ event_seq < MaxSeq
    /\ store[id] = "nil"
    /\ data # "nil"
    /\ store' = [store EXCEPT ![id] = data]
    /\ event_seq' = event_seq + 1
    /\ outbox' = outbox \cup {[seq |-> event_seq, op |-> "create", retries |-> 0]}
    /\ UNCHANGED dead_letter

DeliverEvent(entry) ==
    /\ entry \in outbox
    /\ outbox' = outbox \ {entry}
    /\ UNCHANGED <<store, dead_letter, event_seq>>

(* BUG: Missing guard "entry.retries < MaxRetries" *)
RetryEvent(entry) ==
    /\ entry \in outbox
    (* /\ entry.retries < MaxRetries  <- MISSING! *)
    /\ outbox' = (outbox \ {entry}) \cup {[entry EXCEPT !.retries = @ + 1]}
    /\ UNCHANGED <<store, dead_letter, event_seq>>

Next ==
    \/ \E i \in Ids, v \in Values : Create(i, v)
    \/ \E entry \in outbox : DeliverEvent(entry)
    \/ \E entry \in outbox : RetryEvent(entry)

InvRetryBounded ==
    \A entry \in outbox : entry.retries <= MaxRetries

====
