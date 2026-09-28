---- MODULE ConLive ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x < 3 /\ x' = x + 1 /\ y' = y
Flip == y' = 1 - y /\ x' = x
Next == Inc \/ Flip
Spec == Init /\ [][Next]_vars /\ WF_vars(Inc)
SpecS == Init /\ [][Next]_vars /\ SF_vars(Inc)
SpecNF == Init /\ [][Next]_vars
SpecFlip == Init /\ [][Next]_vars /\ WF_vars(Flip)
Con == x < 2
P == <>(x = 3)
PY == []<>(y = 1)
PX1 == <>(x = 1)
====
