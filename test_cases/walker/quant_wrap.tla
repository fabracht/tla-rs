---- MODULE quant_wrap ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Next == (\A i \in {1} : x' \in {1,2} /\ y' = x' + 50) \/ UNCHANGED vars
Inv == y # 52
====
