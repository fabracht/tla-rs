---- MODULE unused_unsupported_definitions ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Hidden == \EE y : x = y
Local == LET I == INSTANCE Naturals IN 1
Inv == x \in {0, 1}
====
Notes after the end of the module are not part of it.
