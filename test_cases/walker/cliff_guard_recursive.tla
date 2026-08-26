---- MODULE cliff_guard_recursive ----
EXTENDS Naturals
VARIABLE x
RECURSIVE Sum(_)
Sum(n) == IF n = 0 THEN 0 ELSE n + Sum(n - 1)
Guard == \A i \in 1..30 : (Sum(3) >= 0 \/ i < 100)
Init == x = 0
Next == Guard /\ x' = 1
Inv == TRUE
====
