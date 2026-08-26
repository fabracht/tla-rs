---- MODULE whole_then_indexed ----
VARIABLE f
Init == f = [i \in {1, 2} |-> 0]
Next == f' = [i \in {1, 2} |-> 9] /\ f'[1] = 5
Inv == TRUE
====
