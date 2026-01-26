---- MODULE fairness_violation ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Inc == x < 2 /\ x' = x + 1

Stay == x' = x

Next == Inc \/ Stay

TypeOK == x \in 0..2

Spec == Init /\ [][Next]_x /\ WF_x(Inc)

====
