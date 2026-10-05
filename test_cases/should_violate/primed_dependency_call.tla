---- MODULE primed_dependency_call ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
IsTwice(a, b) == a = 2 * b
Init == x = 0 /\ y = 0
Step == /\ x' \in {1, 2}
        /\ (y' = 5 \/ IsTwice(y', x'))
Next == Step \/ UNCHANGED vars
Inv == y # 4
====
