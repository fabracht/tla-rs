---- MODULE liveness_test ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Inc == x < 5 /\ x' = x + 1

Next == Inc \/ (x = 5 /\ UNCHANGED x)

TypeOK == x \in 0..5

====
