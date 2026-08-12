---- MODULE unassigned_var ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
Bump == x' = 1 - x
Next == Bump \/ (x' = x /\ y' = y)
Inv == TRUE
====
