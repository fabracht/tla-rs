---- MODULE extended_next ----
EXTENDS Naturals, Lib2
VARIABLES x, y
Init == x = 0 /\ y = 0
Step(k) == x < k /\ x' = x + 1 /\ y' = y
Next == Outer(Step, 2)
====
