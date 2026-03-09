---- MODULE extends_cycle ----
EXTENDS CycleA

VARIABLES x

Init == x = Foo
Next == x' = x
Inv == x = 1
====
