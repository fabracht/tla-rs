---- MODULE indexed_forall_conflict ----
EXTENDS Naturals
VARIABLE f
Init == f = <<0, 0>>
Next == ((\A p \in {1,2} : f'[p] = 0) /\ f'[1] = 9) \/ UNCHANGED f
Inv == f[1] # 9
====
