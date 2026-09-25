---- MODULE Walk3Dead ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Step == x < 2 /\ x' = x + 1
Next == Step
SpecF == Init /\ [][Next]_x /\ WF_x(Step)
SpecNF == Init /\ [][Next]_x

PropEventually == <>(x = 2)
PropInfOften == []<>(x = 2)
====
