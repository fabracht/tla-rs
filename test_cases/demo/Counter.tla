---- MODULE Counter ----
EXTENDS Integers
CONSTANT Max
VARIABLES x, overflow

Init == x = 0 /\ overflow = FALSE

Inc ==
    /\ x' = x + 1
    /\ overflow' = (x + 1 > Max)

Reset ==
    /\ x' = 0
    /\ overflow' = overflow

Next == Inc \/ Reset
====
