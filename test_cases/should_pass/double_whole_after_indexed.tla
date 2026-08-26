---- MODULE double_whole_after_indexed ----
g == <<5, 9>>
h == <<5, 2>>
VARIABLE f
Init == f = <<0, 0>>
Next == (f'[1] = 5 /\ f' = g /\ f' = h) \/ UNCHANGED f
Inv == f[2] # 2
====
