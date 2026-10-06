---- MODULE let_next ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
Step(k) == x < k /\ x' = x + 1 /\ y' = y
Apply(F(_), v) == F(v)
Next == LET S(k) == Step(k) IN Apply(S, 2)
====
