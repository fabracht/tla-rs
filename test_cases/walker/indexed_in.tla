---- MODULE indexed_in ----
VARIABLE f
Init == f = [i \in {1, 2} |-> 0]
Next == f'[1] \in {5, 6} /\ f'[2] = 0
Inv == f[1] # 5
====
