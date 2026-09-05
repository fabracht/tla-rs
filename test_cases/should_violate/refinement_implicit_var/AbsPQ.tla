---- MODULE AbsPQ ----
EXTENDS Integers
VARIABLES p, q
AInit == p = 0 /\ q = 0
ANext == p' = p + 1 /\ q' = q
====
