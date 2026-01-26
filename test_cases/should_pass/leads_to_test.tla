---- MODULE leads_to_test ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Inc == x < 5 /\ x' = x + 1

Next == Inc \/ (x = 5 /\ UNCHANGED x)

TypeOK == x \in 0..5

Spec == Init /\ [][Next]_x /\ ((x = 0) ~> (x = 5))

====
