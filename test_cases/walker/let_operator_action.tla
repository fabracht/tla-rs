---- MODULE let_operator_action ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == LET Bump(n) == n + 1 IN x' = Bump(x)
Inv == x < 3
====
