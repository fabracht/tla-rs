---- MODULE SubVars ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A == y = 0 /\ y' = 1 /\ UNCHANGED x
Next == A \/ UNCHANGED vars
SX == Init /\ [][Next]_vars /\ WF_x(A)
SV == Init /\ [][Next]_vars /\ WF_vars(A)

PropC34 == <>(y = 1)
====
