---- MODULE parameterized_inv_prefix ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Next == x' = x + 1

InvokeAction(p) == p > 0

InitNode(k) == [key |-> k]

NextStep(n) == n + 1

InvCounter == x \in 0..1000
====
