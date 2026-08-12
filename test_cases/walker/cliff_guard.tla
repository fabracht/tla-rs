---- MODULE cliff_guard ----
EXTENDS Naturals
VARIABLE x
Guard == \A i \in 1..24 : (i > 0 \/ i < 100)
Init == x = 0
Next == Guard /\ x' = 1
Inv == TRUE
====
