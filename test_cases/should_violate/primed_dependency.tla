---- MODULE primed_dependency ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Step == /\ x' \in {1, 2}
        /\ (y' = 5 \/ y' = 2 * x')
Next == Step \/ UNCHANGED vars
Inv == y # 4
====
