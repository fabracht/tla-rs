---- MODULE fairness_test ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Inc == x < 5 /\ x' = x + 1

Dec == x > 0 /\ x' = x - 1

Next == Inc \/ Dec

TypeOK == x \in 0..5

Spec == Init /\ [][Next]_x /\ WF_x(Inc)

====
