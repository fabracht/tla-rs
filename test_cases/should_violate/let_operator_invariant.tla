---- MODULE let_operator_invariant ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == LET Double(n) == n * 2 IN Double(x) < 8
====
