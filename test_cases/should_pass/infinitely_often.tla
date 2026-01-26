---- MODULE infinitely_often ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Toggle == x' = 1 - x

Next == Toggle

TypeOK == x \in 0..1

Spec == Init /\ [][Next]_x /\ []<>(x = 0)

====
