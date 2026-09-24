---- MODULE Walk2 ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Step == x < 1 /\ x' = x + 1
Next == Step \/ UNCHANGED x
SpecF == Init /\ [][Next]_x /\ WF_x(Step)

PropC19 == (x = 0) ~> (x = 2)
PropC20 == [](x = 0 => <>(x = 2))
PropC21 == \E i \in {1, 2} : <>(x = i)
PropC22 == \A i \in {1, 2} : <>(x = i)
====
