---- MODULE MQDBOutbox ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    OperationIds,
    EventsPerOp,
    MaxRetries

VARIABLES
    outbox,
    dead_letter,
    delivery_count,
    dispatching,
    dispatch_idx

vars == <<outbox, dead_letter, delivery_count, dispatching, dispatch_idx>>

OutboxEntry == [
    op_id: OperationIds,
    num_events: 1..EventsPerOp,
    retries: 0..MaxRetries
]

EventKey == OperationIds \times (1..EventsPerOp)

TypeOK ==
    /\ outbox \subseteq OutboxEntry
    /\ dead_letter \subseteq OperationIds
    /\ DOMAIN delivery_count = EventKey
    /\ dispatching \in OperationIds \cup {"none"}
    /\ dispatch_idx \in 0..EventsPerOp

Init ==
    /\ outbox = {[op_id |-> op, num_events |-> EventsPerOp, retries |-> 0] : op \in OperationIds}
    /\ dead_letter = {}
    /\ delivery_count = [k \in EventKey |-> 0]
    /\ dispatching = "none"
    /\ dispatch_idx = 0

StartDispatch(entry) ==
    /\ entry \in outbox
    /\ dispatching = "none"
    /\ entry.retries < MaxRetries
    /\ dispatching' = entry.op_id
    /\ dispatch_idx' = 1
    /\ UNCHANGED <<outbox, dead_letter, delivery_count>>

DispatchEventSuccess ==
    /\ dispatching # "none"
    /\ dispatch_idx > 0
    /\ LET entry == CHOOSE e \in outbox : e.op_id = dispatching
           key == <<dispatching, dispatch_idx>>
       IN /\ delivery_count' = [delivery_count EXCEPT ![key] = @ + 1]
          /\ IF dispatch_idx = entry.num_events
             THEN /\ outbox' = outbox \ {entry}
                  /\ dispatching' = "none"
                  /\ dispatch_idx' = 0
             ELSE /\ dispatch_idx' = dispatch_idx + 1
                  /\ UNCHANGED <<outbox, dispatching>>
    /\ UNCHANGED dead_letter

DispatchEventFailure ==
    /\ dispatching # "none"
    /\ dispatch_idx > 0
    /\ dispatching' = "none"
    /\ dispatch_idx' = 0
    /\ LET entry == CHOOSE e \in outbox : e.op_id = dispatching
       IN IF entry.retries + 1 >= MaxRetries
          THEN /\ dead_letter' = dead_letter \cup {entry.op_id}
               /\ outbox' = outbox \ {entry}
          ELSE /\ outbox' = (outbox \ {entry}) \cup
                    {[entry EXCEPT !.retries = @ + 1]}
               /\ UNCHANGED dead_letter
    /\ UNCHANGED delivery_count

MoveToDeadLetter(entry) ==
    /\ entry \in outbox
    /\ dispatching = "none"
    /\ entry.retries >= MaxRetries
    /\ dead_letter' = dead_letter \cup {entry.op_id}
    /\ outbox' = outbox \ {entry}
    /\ UNCHANGED <<delivery_count, dispatching, dispatch_idx>>

Next ==
    \/ \E entry \in outbox : StartDispatch(entry)
    \/ DispatchEventSuccess
    \/ DispatchEventFailure
    \/ \E entry \in outbox : MoveToDeadLetter(entry)

Spec == Init /\ [][Next]_vars

InvNoDoubleDelivery ==
    \A key \in EventKey : delivery_count[key] <= 1

InvDeadLetterNotInOutbox ==
    \A entry \in outbox : entry.op_id \notin dead_letter

InvDispatchingInOutbox ==
    dispatching # "none" => \E e \in outbox : e.op_id = dispatching

====
