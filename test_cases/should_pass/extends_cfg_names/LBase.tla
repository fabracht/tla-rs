---- MODULE LBase ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Inc == x < 3 /\ x' = x + 1
Next == Inc \/ (x = 3 /\ x' = 3)
Spec == Init /\ [][Next]_x /\ WF_x(Inc)
Reach == <>(x = 3)
Bounded == x <= 3
SpecNoFair == Init /\ [][Next]_x
====
