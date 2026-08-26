---- MODULE indexed_then_whole_assignment ----
g == <<5, 9>>
VARIABLE f
Init == f = <<0, 0>>
Next == (f'[1] = 5 /\ f' = g) \/ UNCHANGED f
Inv == f[2] # 9
====
