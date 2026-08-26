---- MODULE init_disjunct ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ (y = 1 \/ \E v \in {2, 3} : y = v)
Next == UNCHANGED <<x, y>>
Inv == y # 3
====
