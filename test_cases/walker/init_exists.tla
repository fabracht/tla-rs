---- MODULE init_exists ----
EXTENDS Naturals
VARIABLES x
Init == \E v \in {1, 2} : x = v
Next == UNCHANGED x
Inv == x # 2
====
