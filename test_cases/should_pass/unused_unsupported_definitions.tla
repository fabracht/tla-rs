---- MODULE unused_unsupported_definitions ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Pairs == [i \in 1..2, j \in 1..2 |-> i + j]
Hidden == \EE y : x = y
f[n \in 1..3] == n
Inv == x \in {0, 1}
====
Notes after the end of the module are not part of it.
