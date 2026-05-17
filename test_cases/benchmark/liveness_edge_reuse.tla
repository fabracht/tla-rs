------------------------------ MODULE liveness_edge_reuse ------------------------------

EXTENDS Naturals

CONSTANT Max

VARIABLE x

Init ==
    x = 0

Next ==
    \/ /\ x < Max
       /\ x' = x + 1
    \/ /\ x > 0
       /\ x' = x - 1

EventuallyZero ==
    <> (x = 0)

=============================================================================
