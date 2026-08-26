---- MODULE equality_binds_unbound_prime ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = 1 /\ x' = y'
Inv == TRUE
====
