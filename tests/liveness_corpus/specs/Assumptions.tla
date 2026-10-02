---- MODULE Assumptions ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x < 2 /\ x' = x + 1 /\ y' = y
Flip == y' = 1 - y /\ x' = x
Next == Inc \/ Flip
LiveP(v) == <>[](x = v)
SpecE == Init /\ [][Next]_vars /\ (\E v \in {2} : <>[](x = v))
SpecImp == Init /\ [][Next]_vars /\ ((x = 0) => <>(x = 2))
SpecNot == Init /\ [][Next]_vars /\ ~<>[](x = 0)
SpecCall == Init /\ [][Next]_vars /\ LiveP(2)
SpecQCall == Init /\ [][Next]_vars /\ (\A v \in {2} : LiveP(v))
SpecMix == Init /\ [][Next]_vars /\ (\A v \in {2} : (LiveP(v) /\ WF_vars(Flip)))
SpecF == Init /\ [][Next]_vars /\ WF_vars(Inc)
Reach2 == <>(x = 2)
LetTemp == LET a == <>(x = 2) IN a
LetNot == LET a == <>(x = 2) IN ~a
LetDom == LET w(p) == x = p IN \A p \in {0, 1} : w(p) ~> (x = 2)
====
