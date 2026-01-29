---- MODULE MQDBConsumerGroup ----
EXTENDS Naturals, FiniteSets

CONSTANTS Consumers, Groups, Partitions, MaxTime, HeartbeatTimeout

VARIABLES members, assignments, heartbeat, time

vars == <<members, assignments, heartbeat, time>>

Init ==
    /\ members = [g \in Groups |-> {}]
    /\ assignments = [g \in Groups |-> [p \in Partitions |-> "none"]]
    /\ heartbeat = [c \in Consumers |-> 0]
    /\ time = 0

AssignPartitions(ms) ==
    IF ms = {}
    THEN [p \in Partitions |-> "none"]
    ELSE CHOOSE assignment \in [Partitions -> ms] : TRUE

JoinGroup(group, consumer) ==
    /\ consumer \notin members[group]
    /\ LET new_ms == members[group] \cup {consumer}
       IN /\ members' = [members EXCEPT ![group] = new_ms]
          /\ assignments' = [assignments EXCEPT ![group] = AssignPartitions(new_ms)]
    /\ heartbeat' = [heartbeat EXCEPT ![consumer] = time]
    /\ UNCHANGED time

LeaveGroup(group, consumer) ==
    /\ consumer \in members[group]
    /\ LET new_ms == members[group] \ {consumer}
       IN /\ members' = [members EXCEPT ![group] = new_ms]
          /\ assignments' = [assignments EXCEPT ![group] = AssignPartitions(new_ms)]
    /\ UNCHANGED <<heartbeat, time>>

SendHeartbeat(consumer) ==
    /\ \E g \in Groups : consumer \in members[g]
    /\ heartbeat' = [heartbeat EXCEPT ![consumer] = time]
    /\ UNCHANGED <<members, assignments, time>>

Tick ==
    /\ time < MaxTime
    /\ time' = time + 1
    /\ UNCHANGED <<members, assignments, heartbeat>>

RemoveStaleConsumer(group, consumer) ==
    /\ consumer \in members[group]
    /\ time - heartbeat[consumer] > HeartbeatTimeout
    /\ LET new_ms == members[group] \ {consumer}
       IN /\ members' = [members EXCEPT ![group] = new_ms]
          /\ assignments' = [assignments EXCEPT ![group] = AssignPartitions(new_ms)]
    /\ UNCHANGED <<heartbeat, time>>

Next ==
    \/ \E g \in Groups, c \in Consumers : JoinGroup(g, c)
    \/ \E g \in Groups, c \in Consumers : LeaveGroup(g, c)
    \/ \E c \in Consumers : SendHeartbeat(c)
    \/ Tick
    \/ \E g \in Groups, c \in Consumers : RemoveStaleConsumer(g, c)

InvNoGapsWhenMembersExist ==
    \A g \in Groups :
        (members[g] # {} => (\A p \in Partitions : assignments[g][p] # "none"))

InvAllAssignedAreMembers ==
    \A g \in Groups : \A p \in Partitions :
        (assignments[g][p] # "none" => assignments[g][p] \in members[g])

InvEmptyGroupNoAssignments ==
    \A g \in Groups :
        (members[g] = {} => (\A p \in Partitions : assignments[g][p] = "none"))

InvStaleConsumersCanBeRemoved ==
    \A g \in Groups, c \in Consumers :
        (c \in members[g] /\ time - heartbeat[c] > HeartbeatTimeout) =>
        (LET new_ms == members[g] \ {c}
         IN TRUE)

====
