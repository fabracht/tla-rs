---- MODULE Assume ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Step == x < 2 /\ x' = x + 1
Next == Step \/ UNCHANGED x
SpecA == Init /\ [][Next]_x /\ <>(x = 2)

PropC40 == <>(x = 2)
====
