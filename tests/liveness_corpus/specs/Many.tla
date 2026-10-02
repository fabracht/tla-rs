---- MODULE Many ----
EXTENDS Naturals
VARIABLE c
Init == c = [i \in 1..12 |-> 0]
Toggle(i) == c' = [c EXCEPT ![i] = 1 - c[i]]
Next == \E i \in 1..12 : Toggle(i)
Spec == Init /\ [][Next]_c /\ \A i \in 1..12 : WF_c(Toggle(i))
SomeStable == \E i \in 1..12 : <>[](c[i] # 0)
AllRecur == \A i \in 1..12 : []<>(c[i] = 1)
====
