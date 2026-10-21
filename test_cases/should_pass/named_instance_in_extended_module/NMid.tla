---- MODULE NMid ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
I == INSTANCE NInner WITH y <- x
Inv == I!Ok
====
