---- MODULE if_rhs ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Next == (x' \in {1, 2} /\ y' = (IF x' = 1 THEN 10 ELSE 20)) \/ UNCHANGED vars
Inv == y # 20
====
