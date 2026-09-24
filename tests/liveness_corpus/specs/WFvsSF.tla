---- MODULE WFvsSF ----
EXTENDS Naturals
VARIABLES b, y
vars == <<b, y>>
Init == b = FALSE /\ y = 0
Flip == b' = ~b /\ UNCHANGED y
A == b /\ y = 0 /\ y' = 1 /\ UNCHANGED b
Next == Flip \/ A
SWF == Init /\ [][Next]_vars /\ WF_vars(Flip) /\ WF_vars(A)
SSF == Init /\ [][Next]_vars /\ WF_vars(Flip) /\ SF_vars(A)

PropC28 == <>(y = 1)
PropC30 == []<>b
====
