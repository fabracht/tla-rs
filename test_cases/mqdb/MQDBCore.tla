---- MODULE MQDBCore ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ids, Values, MaxRetries, MaxSeq

VARIABLES store, outbox, dead_letter, delivered, event_seq

vars == <<store, outbox, dead_letter, delivered, event_seq>>

Init ==
    /\ store = [i \in Ids |-> "nil"]
    /\ outbox = {}
    /\ dead_letter = {}
    /\ delivered = {}
    /\ event_seq = 0

Create(id, data) ==
    /\ event_seq < MaxSeq
    /\ store[id] = "nil"
    /\ data # "nil"
    /\ store' = [store EXCEPT ![id] = data]
    /\ event_seq' = event_seq + 1
    /\ outbox' = outbox \cup {[seq |-> event_seq, op |-> "create", retries |-> 0]}
    /\ UNCHANGED <<dead_letter, delivered>>

Update(id, data) ==
    /\ event_seq < MaxSeq
    /\ store[id] # "nil"
    /\ data # "nil"
    /\ data # store[id]
    /\ store' = [store EXCEPT ![id] = data]
    /\ event_seq' = event_seq + 1
    /\ outbox' = outbox \cup {[seq |-> event_seq, op |-> "update", retries |-> 0]}
    /\ UNCHANGED <<dead_letter, delivered>>

Delete(id) ==
    /\ event_seq < MaxSeq
    /\ store[id] # "nil"
    /\ store' = [store EXCEPT ![id] = "nil"]
    /\ event_seq' = event_seq + 1
    /\ outbox' = outbox \cup {[seq |-> event_seq, op |-> "delete", retries |-> 0]}
    /\ UNCHANGED <<dead_letter, delivered>>

DeliverEvent(entry) ==
    /\ entry \in outbox
    /\ outbox' = outbox \ {entry}
    /\ delivered' = delivered \cup {entry.seq}
    /\ UNCHANGED <<store, dead_letter, event_seq>>

RetryEvent(entry) ==
    /\ entry \in outbox
    /\ entry.retries < MaxRetries
    /\ outbox' = (outbox \ {entry}) \cup {[entry EXCEPT !.retries = @ + 1]}
    /\ UNCHANGED <<store, dead_letter, delivered, event_seq>>

MoveToDeadLetter(entry) ==
    /\ entry \in outbox
    /\ entry.retries >= MaxRetries
    /\ dead_letter' = dead_letter \cup {entry.seq}
    /\ outbox' = outbox \ {entry}
    /\ UNCHANGED <<store, delivered, event_seq>>

Next ==
    \/ \E i \in Ids, v \in Values : Create(i, v)
    \/ \E i \in Ids, v \in Values : Update(i, v)
    \/ \E i \in Ids : Delete(i)
    \/ \E entry \in outbox : DeliverEvent(entry)
    \/ \E entry \in outbox : RetryEvent(entry)
    \/ \E entry \in outbox : MoveToDeadLetter(entry)

InvMonotonicSequence == event_seq >= 0

InvDeadLetterNotInOutbox ==
    \A entry \in outbox : entry.seq \notin dead_letter

InvRetryBounded ==
    \A entry \in outbox : entry.retries <= MaxRetries

InvEventNotLost ==
    \A seq \in 0..(event_seq - 1) :
        (\E e \in outbox : e.seq = seq) \/
        (seq \in dead_letter) \/
        (seq \in delivered)

====
