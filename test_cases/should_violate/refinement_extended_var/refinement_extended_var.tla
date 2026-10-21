---- MODULE refinement_extended_var ----
EXTENDS Naturals
VARIABLE x
A == INSTANCE RExtAbs WITH y <- x
Init == x = 0
Next == x < 3 /\ x' = x + 2
====
