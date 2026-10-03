---- MODULE liveness_error ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x < 2 /\ x' = x + 1 /\ y' = y
OnlyX == x' = x
Spec == Init /\ [][Inc]_vars /\ WF_vars(Inc)
FairOnlyX == WF_vars(OnlyX)
====
