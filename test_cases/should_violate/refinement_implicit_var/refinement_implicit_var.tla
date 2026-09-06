---- MODULE refinement_implicit_var ----
EXTENDS Integers
VARIABLES p, q
A == INSTANCE AbsPQ WITH p <- p
Init == p = 0 /\ q = 0
Next == (q < 3) /\ (p' = p /\ q' = q + 1)
Inv == q <= 3
====
