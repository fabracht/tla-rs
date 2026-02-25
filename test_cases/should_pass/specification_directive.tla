---- MODULE specification_directive ----
EXTENDS Naturals

VARIABLES x

Init == x = 0

Next == x' = (x + 1) % 4

vars == <<x>>

Spec == Init /\ [][Next]_vars

TypeOK == x \in 0..3

====
