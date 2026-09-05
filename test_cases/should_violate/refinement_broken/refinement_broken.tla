---- MODULE refinement_broken ----
EXTENDS Naturals
VARIABLE x
A == INSTANCE AbsCounter WITH ac <- x
Init == x = 0
Next == (x < 4) /\ (x' = x + 2)
Inv == x <= 4
====
