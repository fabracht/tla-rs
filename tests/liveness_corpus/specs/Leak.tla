---- MODULE Leak ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Step == x < 1 /\ x' = x + 1
Nxt == Step \/ UNCHANGED x
Spec == Init /\ [][Nxt]_x
FairSpec == Init /\ [][Nxt]_x /\ WF_x(Step)
ReachOne == <>(x = 1)
====
