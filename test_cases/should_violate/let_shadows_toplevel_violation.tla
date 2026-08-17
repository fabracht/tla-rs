---- MODULE let_shadows_toplevel_violation ----
EXTENDS Naturals
VARIABLE x
G(n) == 0
Init == x = 0
Next == x' = x + 1 /\ x < 3
Inv == LET G(n) == 1000 IN G(x) < 50
====
