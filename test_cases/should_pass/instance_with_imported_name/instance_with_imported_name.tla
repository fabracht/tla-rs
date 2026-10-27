---- MODULE instance_with_imported_name ----
VARIABLE x
INSTANCE M4 WITH C <- 1
I == INSTANCE X4 WITH D <- Val
Init == x = 0
Next == UNCHANGED x
InvA == I!Foo = 1
====
