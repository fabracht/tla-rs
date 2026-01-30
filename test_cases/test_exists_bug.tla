---- MODULE test_exists_bug ----
CONSTANT Nodes
VARIABLE alive

Init == alive = [n \in Nodes |-> TRUE]

Next == UNCHANGED alive

InvExistsSimple == \E n \in Nodes : n \in Nodes

InvExistsAnd == \E n \in Nodes : alive[n] /\ n \in Nodes

InvExistsMultipleAnd == \E n \in Nodes : n \in Nodes /\ alive[n] /\ n \in Nodes

InvExistsEq == \E n \in Nodes : alive[n] = TRUE /\ n \in Nodes

====
