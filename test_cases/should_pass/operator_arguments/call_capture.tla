---- MODULE call_capture ----
EXTENDS Naturals
VARIABLE s
Init == s = 0
Next == UNCHANGED s
Apply(F(_), v) == F(v)
Apply2(w, F(_)) == F(w)
Pair(a, b) == <<a, b>>
Lt(n) == n < 5
InvCapture == \E v \in {5} : Apply(LAMBDA a : a < v, 3)
InvLaterParam == LET F(n) == n + 100 IN ~Apply2(F(1), Lt)
InvPair == \E b \in {7} : Pair(b, 1) = <<7, 1>>
====
