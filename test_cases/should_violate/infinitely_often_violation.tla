---- MODULE infinitely_often_violation ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Inc == x < 3 /\ x' = x + 1

Stutter == x = 3 /\ UNCHANGED x

Next == Inc \/ Stutter

TypeOK == x \in 0..3

Spec == Init /\ [][Next]_x /\ []<>(x = 0)

====
