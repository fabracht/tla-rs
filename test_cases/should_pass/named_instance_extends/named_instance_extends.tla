---- MODULE named_instance_extends ----
EXTENDS Naturals
VARIABLE x
Foo == 100
I == INSTANCE NExtMid WITH y <- x
Init == x = 0
Next == x < 2 /\ x' = x + 1
InvFoo == I!Foo = 7
InvBar == I!Bar = 8
InvBaz == I!Baz = 3
InvOk == I!Ok
InvRoot == Foo = 100
====
