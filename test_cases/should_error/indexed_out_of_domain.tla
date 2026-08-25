---- MODULE indexed_out_of_domain ----
VARIABLE f
Init == f = [i \in {1, 2} |-> 0]
Next == f' = [i \in {1, 2} |-> 9] /\ f'[5] = 9
Inv == TRUE
====
