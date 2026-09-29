---- MODULE Classify ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Step == x < 2 /\ x' = x + 1 /\ y' = y
Swap == x = 2 /\ y = 0 /\ y' = 1 /\ x' = x
Next == Step \/ Swap
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

QInvOk == \A i \in {1, 2} : [](x # i + 5)
QInvBad == \A i \in {1, 2} : [](x # i)
ActVarsOk == [][x' >= x /\ y' >= y]_vars
ActVarsBad == [][y' = y]_vars
InitOr == x = 0 \/ x = 5
InitOrBad == x = 3 \/ y = 1
QActBad == \A i \in {0, 1} : [][x' # i + 2]_x
MixLiveBad == [](x < 3) /\ <>(y = 2)
MixOk == [](y < 2) /\ [][x' >= x]_x /\ <>(y = 1) /\ x = 0
====
