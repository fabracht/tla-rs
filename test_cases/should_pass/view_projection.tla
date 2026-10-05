---- MODULE view_projection ----
EXTENDS Integers
VARIABLES x, aux
Init == x = 0 /\ aux = 0
Next == x < 3 /\ x' = x + 1 /\ aux' = aux + 1
Small == x < 9
Project == x
====
