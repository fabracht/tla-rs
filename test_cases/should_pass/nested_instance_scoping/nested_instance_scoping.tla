---- MODULE nested_instance_scoping ----
EXTENDS Naturals, NSExt
VARIABLE x
INSTANCE NSMid WITH y <- x
I == INSTANCE NSM WITH C <- 5
Init == x = 0 /\ w = 10
Next == x < 2 /\ x' = x + 1 /\ w' = w
InvCopies == ReadW = w /\ Read = x
InvImplicit == I!ReadC = 1
====
