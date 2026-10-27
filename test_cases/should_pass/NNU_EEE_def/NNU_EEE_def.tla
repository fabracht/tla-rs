---- MODULE NNU_EEE_def ----
EXTENDS Naturals
VARIABLE x
CONSTANT C3
I == INSTANCE NNU_EEE_defA WITH w <- x, C3 <- 7
Read0 == I!Read1
Init == x = 0
Next == x < 2 /\ x' = x + 1
InvRead == Read0 = 2 * x + 19
====
