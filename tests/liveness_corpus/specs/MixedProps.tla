---- MODULE MixedProps ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Step == x' = (x + 1) % 6
Spec == Init /\ [][Step]_x /\ WF_x(Step)
LTSafe == [](x = 0 => <>(x = 2)) /\ [](x < 5)
EvSafe == <>(x = 2) /\ [](x < 5)
LTAlone == [](x = 0 => <>(x = 2))
LTOr == [](x = 0 => <>(x = 9)) \/ [](x = 0 => <>(x = 2))
====
