---- MODULE MQDBCore_BugLostEvent ----
(* BUG: Event can be removed from outbox without delivery or dead-letter
   This violates InvEventNotLost - events must be tracked until handled *)
EXTENDS Naturals, FiniteSets

CONSTANTS Ids, Values, MaxRetries, MaxSeq

VARIABLES store, outbox, dead_letter, event_seq, delivered

Init ==
    /\ store = [i \in Ids |-> "nil"]
    /\ outbox = {}
    /\ dead_letter = {}
    /\ event_seq = 0
    /\ delivered = {}

Create(id, data) ==
    /\ event_seq < MaxSeq
    /\ store[id] = "nil"
    /\ data # "nil"
    /\ store' = [store EXCEPT ![id] = data]
    /\ event_seq' = event_seq + 1
    /\ outbox' = outbox \cup {[seq |-> event_seq, op |-> "create", retries |-> 0]}
    /\ UNCHANGED <<dead_letter, delivered>>

DeliverEvent(entry) ==
    /\ entry \in outbox
    /\ outbox' = outbox \ {entry}
    /\ delivered' = delivered \cup {entry.seq}
    /\ UNCHANGED <<store, dead_letter, event_seq>>

(* BUG: Silently drops event without tracking *)
DropEvent(entry) ==
    /\ entry \in outbox
    /\ outbox' = outbox \ {entry}
    /\ UNCHANGED <<store, dead_letter, event_seq, delivered>>

MoveToDeadLetter(entry) ==
    /\ entry \in outbox
    /\ entry.retries >= MaxRetries
    /\ dead_letter' = dead_letter \cup {entry.seq}
    /\ outbox' = outbox \ {entry}
    /\ UNCHANGED <<store, event_seq, delivered>>

Next ==
    \/ \E i \in Ids, v \in Values : Create(i, v)
    \/ \E entry \in outbox : DeliverEvent(entry)
    \/ \E entry \in outbox : DropEvent(entry)
    \/ \E entry \in outbox : MoveToDeadLetter(entry)

(* Every created event must be either: in outbox, delivered, or dead-lettered *)
InvEventNotLost ==
    \A s \in 0..(event_seq - 1) :
        \/ \E entry \in outbox : entry.seq = s
        \/ s \in delivered
        \/ s \in dead_letter

====
