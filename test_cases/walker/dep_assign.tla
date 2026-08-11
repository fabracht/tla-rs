---- MODULE dep_assign ----
EXTENDS Naturals
VARIABLES a, b
vars == <<a, b>>
Init == a = 0 /\ b = 0
Next == (a' \in {1, 2} /\ b' = a' + 10) \/ UNCHANGED vars
Inv == b # 12
====
