---- MODULE multi_fairness ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

ActionA == x < 3 /\ x' = x + 1

ActionB == x = 3 /\ x' = 0

Next == ActionA \/ ActionB

TypeOK == x \in 0..3

Spec == Init /\ [][Next]_x /\ WF_x(ActionA) /\ SF_x(ActionB)

====
