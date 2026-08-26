---- MODULE let_shadows_toplevel ----
EXTENDS Naturals
VARIABLE x
G(n) == 1000
c == 1000
Init == x = 0
Next == x' = x + 1 /\ x < 3
Inv == (LET G(n) == 0 IN G(x) < 50) /\ (LET c == 0 IN c < 50)
====
