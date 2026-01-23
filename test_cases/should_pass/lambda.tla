---- MODULE lambda ----
EXTENDS Naturals

VARIABLES x

Init == x = 0

double == LAMBDA n : n * 2

Next == x' = double[x] /\ x < 5

Inv == x <= 10 /\ x >= 0

====
