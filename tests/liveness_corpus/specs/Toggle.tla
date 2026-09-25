---- MODULE Toggle ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = 1 - x
SpecF == Init /\ [][Next]_x /\ WF_x(Next)
SpecNF == Init /\ [][Next]_x

PropC23 == []<>(x = 0) /\ []<>(x = 1)
PropC24 == <>[](x = 1)
PropC25 == []<>(x = 0) \/ []<>(x = 1)
PropC26 == []((x = 0) => <>(x = 1))
PropC27 == []<>(x = 1)
PropC38 == []<><<Next>>_x
PropC39 == <>[][FALSE]_x
PropC41 == [][x' >= x]_x
====
