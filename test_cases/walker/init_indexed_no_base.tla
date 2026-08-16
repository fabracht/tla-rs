---- MODULE init_indexed_no_base ----
VARIABLE f
Init == f[1] = 5 /\ f[2] = 0
Next == UNCHANGED f
Inv == TRUE
====
