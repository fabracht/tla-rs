---- MODULE MQDBConsumerGroup_BugOrphanPartition ----
(* BUG: Rebalance doesn't assign all partitions when members exist
   This violates InvAllPartitionsAssigned *)
EXTENDS Naturals, FiniteSets

CONSTANTS Consumers, Groups, Partitions

VARIABLES members, assignments

Init ==
    /\ members = [g \in Groups |-> {}]
    /\ assignments = [g \in Groups |-> [p \in Partitions |-> "none"]]

Join(c, g) ==
    /\ c \notin members[g]
    /\ members' = [members EXCEPT ![g] = @ \cup {c}]
    /\ assignments' = assignments  (* BUG: No rebalance on join! *)

Leave(c, g) ==
    /\ c \in members[g]
    /\ members' = [members EXCEPT ![g] = @ \ {c}]
    /\ assignments' = assignments  (* BUG: No rebalance on leave! *)

(* Correct rebalance - but it's never called due to bug above *)
Rebalance(g) ==
    /\ members[g] # {}
    /\ \E f \in [Partitions -> members[g]] :
        assignments' = [assignments EXCEPT ![g] = f]
    /\ UNCHANGED members

Next ==
    \/ \E c \in Consumers, g \in Groups : Join(c, g)
    \/ \E c \in Consumers, g \in Groups : Leave(c, g)

(* When members exist, all partitions should be assigned to some member *)
InvAllPartitionsAssigned ==
    \A g \in Groups :
        members[g] # {} =>
            \A p \in Partitions : assignments[g][p] \in members[g]

====
