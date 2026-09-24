---- MODULE Walk3 ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Step == x < 2 /\ x' = x + 1
Next == Step \/ UNCHANGED x
SpecF == Init /\ [][Next]_x /\ WF_x(Step)
SpecNF == Init /\ [][Next]_x

PropC1 == <>(x = 1)
PropC2 == <>(x = 1) \/ <>(x = 5)
PropC3 == [](x < 5)
PropC4 == [](x = 2 => [](x = 2))
PropC5 == [](x < 2)
PropC6 == x = 1
PropC7 == []<>(x = 1)
PropC8 == <>[](x = 2)
PropC9 == (x = 0) ~> (x = 2)
PropC10 == [](x = 1 => <>[](x = 2))
PropC11 == <>(x = 1 /\ <>(x = 2))
PropC12 == \A i \in {1, 2} : <>(x = i)
PropC13 == \E i \in {1, 5} : []<>(x = i)
PropC14 == <>[](x = 1) \/ <>[](x = 2)
PropC15 == []<>(~ENABLED Step)
PropC16 == <>(x = 2)
PropC17 == <>(x = 0)
PropC18 == (x = 0) ~> (x = 1)
PropC39 == <>[][FALSE]_x
PropC41 == [][x' >= x]_x
PropC44 == [](ENABLED Step => <><<Step>>_x)
====
