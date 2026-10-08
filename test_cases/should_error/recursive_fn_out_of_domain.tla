---- MODULE recursive_fn_out_of_domain ----
EXTENDS Integers
F == LET f[n \in 1..3] == n * f[n - 1] IN f
VARIABLE x
Init == x = 0
Next == x' = x
InvF == F[3] = 6
====
