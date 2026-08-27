---- MODULE imported_op_primed_arg ----
EXTENDS Naturals, Helper
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Step == /\ x' \in {1, 2}
        /\ (y' = 5 \/ IsTwice(y', x'))
Next == Step \/ UNCHANGED vars
Inv == y # 4
====
