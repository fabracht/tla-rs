---- MODULE MQDBOutboxBugNoAtomicity ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Ids,
    MaxRetries

VARIABLES
    store,
    pending_ops,
    outbox,
    dead_letter,
    delivered,
    crashed

vars == <<store, pending_ops, outbox, dead_letter, delivered, crashed>>

OutboxEntry == [
    op_id: Ids,
    retries: 0..MaxRetries
]

TypeOK ==
    /\ DOMAIN store = Ids
    /\ pending_ops \subseteq Ids
    /\ outbox \subseteq OutboxEntry
    /\ dead_letter \subseteq Ids
    /\ delivered \subseteq Ids
    /\ crashed \in BOOLEAN

Init ==
    /\ store = [id \in Ids |-> "nil"]
    /\ pending_ops = {}
    /\ outbox = {}
    /\ dead_letter = {}
    /\ delivered = {}
    /\ crashed = FALSE

CreateData(id) ==
    /\ ~crashed
    /\ store[id] = "nil"
    /\ store' = [store EXCEPT ![id] = "data"]
    /\ pending_ops' = pending_ops \cup {id}
    /\ UNCHANGED <<outbox, dead_letter, delivered, crashed>>

EnqueuePending(id) ==
    /\ ~crashed
    /\ id \in pending_ops
    /\ outbox' = outbox \cup {[op_id |-> id, retries |-> 0]}
    /\ pending_ops' = pending_ops \ {id}
    /\ UNCHANGED <<store, dead_letter, delivered, crashed>>

Crash ==
    /\ ~crashed
    /\ pending_ops # {}
    /\ pending_ops' = {}
    /\ crashed' = TRUE
    /\ UNCHANGED <<store, outbox, dead_letter, delivered>>

Recover ==
    /\ crashed
    /\ crashed' = FALSE
    /\ UNCHANGED <<store, pending_ops, outbox, dead_letter, delivered>>

DispatchSuccess(entry) ==
    /\ ~crashed
    /\ entry \in outbox
    /\ entry.retries < MaxRetries
    /\ delivered' = delivered \cup {entry.op_id}
    /\ outbox' = outbox \ {entry}
    /\ UNCHANGED <<store, pending_ops, dead_letter, crashed>>

DispatchFailure(entry) ==
    /\ ~crashed
    /\ entry \in outbox
    /\ entry.retries < MaxRetries
    /\ IF entry.retries + 1 >= MaxRetries
       THEN /\ dead_letter' = dead_letter \cup {entry.op_id}
            /\ outbox' = outbox \ {entry}
       ELSE /\ outbox' = (outbox \ {entry}) \cup
                {[entry EXCEPT !.retries = @ + 1]}
            /\ UNCHANGED dead_letter
    /\ UNCHANGED <<store, pending_ops, delivered, crashed>>

MoveToDeadLetter(entry) ==
    /\ ~crashed
    /\ entry \in outbox
    /\ entry.retries >= MaxRetries
    /\ dead_letter' = dead_letter \cup {entry.op_id}
    /\ outbox' = outbox \ {entry}
    /\ UNCHANGED <<store, pending_ops, delivered, crashed>>

Next ==
    \/ \E id \in Ids : CreateData(id)
    \/ \E id \in Ids : EnqueuePending(id)
    \/ Crash
    \/ Recover
    \/ \E entry \in outbox : DispatchSuccess(entry)
    \/ \E entry \in outbox : DispatchFailure(entry)
    \/ \E entry \in outbox : MoveToDeadLetter(entry)

Spec == Init /\ [][Next]_vars

InvDataImpliesOutboxOrDelivered ==
    \A id \in Ids : store[id] # "nil" =>
        (\E e \in outbox : e.op_id = id) \/
        (id \in delivered) \/
        (id \in dead_letter) \/
        (id \in pending_ops)

InvDataImpliesEventualDelivery ==
    crashed => \A id \in Ids : store[id] # "nil" =>
        (\E e \in outbox : e.op_id = id) \/
        (id \in delivered) \/
        (id \in dead_letter)

InvDeadLetterNotInOutbox ==
    \A entry \in outbox : entry.op_id \notin dead_letter

====
