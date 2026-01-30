------------------------------ MODULE counter_with_guards -------------------------------
EXTENDS Naturals

VARIABLE count

Init == count = 0

Increment ==
  /\ count < 5
  /\ count' = count + 1

Decrement ==
  /\ count > 0
  /\ count' = count - 1

Reset ==
  /\ count >= 3
  /\ count' = 0

Next == Increment \/ Decrement \/ Reset

InvBounded == count <= 5
=============================================================================
