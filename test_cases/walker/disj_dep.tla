---- MODULE disj_dep ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Next == (x' \in {1,2} /\ (y' = x' * 3 \/ y' = x' * 5)) \/ UNCHANGED vars
Inv == y # 10
====
