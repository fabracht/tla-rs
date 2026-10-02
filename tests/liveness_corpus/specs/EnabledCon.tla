---- MODULE EnabledCon ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Up == x' = x + 1
Next == Up
Spec == Init /\ [][Next]_x
SpecF == Init /\ [][Next]_x /\ WF_x(Up)
Bound == x <= 2
UpOften == []<>ENABLED Up
UpEventuallyOff == <>~ENABLED Up
WFUp == WF_x(Up)
====
