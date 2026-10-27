---- MODULE nested_instance_copies ----
VARIABLE x
INSTANCE M3 WITH C <- 1
I == INSTANCE X3 WITH D <- Val
Init == x = 0
Next == UNCHANGED x
InvA == I!Foo = 1 /\ Val = 1 /\ I!Bar = 2
====
