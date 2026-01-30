---- MODULE MQDBOutboxNoFailure ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    OperationIds,
    EventsPerOp,
    MaxRetries

VARIABLES
    outbox,
    delivery_count,
    dispatching,
    dispatch_idx

vars == <<outbox, delivery_count, dispatching, dispatch_idx>>

OutboxEntry == [
    op_id: OperationIds,
    num_events: 1..EventsPerOp
]

EventKey == OperationIds \times (1..EventsPerOp)

TypeOK ==
    /\ outbox \subseteq OutboxEntry
    /\ DOMAIN delivery_count = EventKey
    /\ dispatching \in OperationIds \cup {"none"}
    /\ dispatch_idx \in 0..EventsPerOp

Init ==
    /\ outbox = {[op_id |-> op, num_events |-> EventsPerOp] : op \in OperationIds}
    /\ delivery_count = [k \in EventKey |-> 0]
    /\ dispatching = "none"
    /\ dispatch_idx = 0

StartDispatch(entry) ==
    /\ entry \in outbox
    /\ dispatching = "none"
    /\ dispatching' = entry.op_id
    /\ dispatch_idx' = 1
    /\ UNCHANGED <<outbox, delivery_count>>

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

Next ==
    \/ \E entry \in outbox : StartDispatch(entry)
    \/ DispatchEventSuccess

Spec == Init /\ [][Next]_vars

InvNoDoubleDelivery ==
    \A key \in EventKey : delivery_count[key] <= 1

InvDispatchingInOutbox ==
    dispatching # "none" => \E e \in outbox : e.op_id = dispatching

====
