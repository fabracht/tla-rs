---- MODULE NNN_EEE ----
EXTENDS Naturals
VARIABLE x
CONSTANT C3
I == INSTANCE NNN_EEEA WITH w <- x, C3 <- 7
Read0 == I!Read1
Init == x = 0
Next == x < 2 /\ x' = x + 1
InvRead == Read0 = 2 * x + 17
InvChain == I!K!J!Val3 = 2 * x + 17
====
