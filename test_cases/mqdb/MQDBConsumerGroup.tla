---- MODULE MQDBConsumerGroup ----
EXTENDS Naturals, FiniteSets

CONSTANTS Consumers, Groups, Partitions

VARIABLES members, assignments

vars == <<members, assignments>>

Init ==
    /\ members = [g \in Groups |-> {}]
    /\ assignments = [g \in Groups |-> [p \in Partitions |-> "none"]]

AssignPartitions(ms) ==
    IF ms = {}
    THEN [p \in Partitions |-> "none"]
    ELSE CHOOSE assignment \in [Partitions -> ms] : TRUE

JoinGroup(group, consumer) ==
    /\ consumer \notin members[group]
    /\ LET new_ms == members[group] \cup {consumer}
       IN /\ members' = [members EXCEPT ![group] = new_ms]
          /\ assignments' = [assignments EXCEPT ![group] = AssignPartitions(new_ms)]

LeaveGroup(group, consumer) ==
    /\ consumer \in members[group]
    /\ LET new_ms == members[group] \ {consumer}
       IN /\ members' = [members EXCEPT ![group] = new_ms]
          /\ assignments' = [assignments EXCEPT ![group] = AssignPartitions(new_ms)]

Next ==
    \/ \E g \in Groups, c \in Consumers : JoinGroup(g, c)
    \/ \E g \in Groups, c \in Consumers : LeaveGroup(g, c)

InvNoGapsWhenMembersExist ==
    \A g \in Groups :
        (members[g] # {} => (\A p \in Partitions : assignments[g][p] # "none"))

InvAllAssignedAreMembers ==
    \A g \in Groups : \A p \in Partitions :
        (assignments[g][p] # "none" => assignments[g][p] \in members[g])

InvEmptyGroupNoAssignments ==
    \A g \in Groups :
        (members[g] = {} => (\A p \in Partitions : assignments[g][p] = "none"))

====
