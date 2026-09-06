---- MODULE refinement_counter ----
EXTENDS Naturals
VARIABLES x, pending
A == INSTANCE AbsCounter WITH ac <- x
Init == x = 0 /\ pending = FALSE
Begin == pending = FALSE /\ pending' = TRUE /\ x' = x
Commit == pending = TRUE /\ x' = x + 1 /\ pending' = FALSE
Next == (x < 3) /\ (Begin \/ Commit)
Inv == x <= 3
====
