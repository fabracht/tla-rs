---- MODULE indexed_conflict ----
EXTENDS Naturals
VARIABLE f
Init == f = <<0, 0>>
Next == (f'[1] = 5 /\ f'[1] = 6) \/ UNCHANGED f
Inv == f[1] # 6
====
