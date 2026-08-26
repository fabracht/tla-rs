---- MODULE indexed_distinct ----
EXTENDS Naturals
VARIABLE f
Init == f = <<0, 0>>
Next == (f'[1] = 5 /\ f'[2] = 6) \/ UNCHANGED f
Inv == f[1] # 5
====
