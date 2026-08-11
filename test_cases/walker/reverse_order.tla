---- MODULE reverse_order ----
EXTENDS Naturals
VARIABLES a, b
vars == <<a, b>>
Init == a = 0 /\ b = 0
Next == (b' \in {1, 2} /\ a' = b' + 100) \/ UNCHANGED vars
Inv == a # 102
====
