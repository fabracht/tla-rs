---- MODULE prime_defined_op ----
EXTENDS Integers

VARIABLES x

NonNegative == x >= 0

Init == x = 5
\* NonNegative' distributes to x' >= 0, so x' = -5 is blocked and the only
\* reachable state is x = 5. If the prime were dropped (x >= 0 = TRUE), x = -5
\* would become reachable and Inv would be violated.
Next == x' = x - 10 /\ NonNegative'

Inv == x >= 0
====
