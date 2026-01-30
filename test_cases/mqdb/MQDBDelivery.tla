---- MODULE MQDBDelivery ----
EXTENDS Naturals, FiniteSets

CONSTANTS Consumers, Partitions, MaxEvents

VARIABLES
    members,
    assignments,
    outbox,
    inflight,
    delivered,
    event_seq

vars == <<members, assignments, outbox, inflight, delivered, event_seq>>

PartitionFor(event_id) == event_id % Cardinality(Partitions)

AssignPartitions(ms) ==
    IF ms = {}
    THEN [p \in Partitions |-> "none"]
    ELSE CHOOSE assignment \in [Partitions -> ms] : TRUE

Init ==
    /\ members = {}
    /\ assignments = [p \in Partitions |-> "none"]
    /\ outbox = {}
    /\ inflight = {}
    /\ delivered = {}
    /\ event_seq = 0

JoinGroup(consumer) ==
    /\ consumer \notin members
    /\ LET new_ms == members \cup {consumer}
       IN /\ members' = new_ms
          /\ assignments' = AssignPartitions(new_ms)
    /\ UNCHANGED <<outbox, inflight, delivered, event_seq>>

LeaveGroup(consumer) ==
    /\ consumer \in members
    /\ LET new_ms == members \ {consumer}
       IN /\ members' = new_ms
          /\ assignments' = AssignPartitions(new_ms)
    /\ UNCHANGED <<outbox, inflight, delivered, event_seq>>

ProduceEvent ==
    /\ event_seq < MaxEvents
    /\ outbox' = outbox \cup {event_seq}
    /\ event_seq' = event_seq + 1
    /\ UNCHANGED <<members, assignments, inflight, delivered>>

StartDelivery(event, consumer) ==
    /\ event \in outbox
    /\ consumer \in members
    /\ assignments[PartitionFor(event)] = consumer
    /\ inflight' = inflight \cup {<<event, consumer>>}
    /\ outbox' = outbox \ {event}
    /\ UNCHANGED <<members, assignments, delivered, event_seq>>

CompleteDelivery(event, consumer) ==
    /\ <<event, consumer>> \in inflight
    /\ inflight' = inflight \ {<<event, consumer>>}
    /\ delivered' = delivered \cup {<<event, consumer>>}
    /\ UNCHANGED <<members, assignments, outbox, event_seq>>

TimeoutConsumer(consumer) ==
    /\ consumer \in members
    /\ LET new_ms == members \ {consumer}
           events_to_requeue == {e \in 0..(event_seq - 1) : <<e, consumer>> \in inflight}
       IN /\ members' = new_ms
          /\ assignments' = AssignPartitions(new_ms)
          /\ outbox' = outbox \cup events_to_requeue
    /\ UNCHANGED <<inflight, delivered, event_seq>>

Next ==
    \/ \E c \in Consumers : JoinGroup(c)
    \/ \E c \in Consumers : LeaveGroup(c)
    \/ ProduceEvent
    \/ \E e \in outbox, c \in Consumers : StartDelivery(e, c)
    \/ \E e \in 0..(event_seq - 1), c \in Consumers : CompleteDelivery(e, c)
    \/ \E c \in Consumers : TimeoutConsumer(c)

InvNoDoubleDelivery ==
    \A e \in 0..(event_seq - 1) :
        Cardinality({c \in Consumers : <<e, c>> \in delivered}) <= 1

====
