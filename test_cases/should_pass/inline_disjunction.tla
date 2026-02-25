---- MODULE inline_disjunction ----
EXTENDS Naturals

VARIABLES x

Init == x = 0

A == x' = 1
B == x' = 2
C == x' = 3
D == x' = 4
E == x' = 5
F == x' = 0

Next ==
    \/ A \/ B \/ C
    \/ D
    \/ E \/ F

TypeOK == x \in 0..5

====
