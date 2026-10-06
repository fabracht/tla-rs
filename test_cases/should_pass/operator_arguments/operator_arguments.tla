---- MODULE operator_arguments ----
EXTENDS HOLib
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Lt(v) == v < 5
Add(a, b) == a + b
Step(k) == x < k /\ x' = x + 1 /\ y' = y
Apply(F(_), v) == F(v)
Fold(Op(_, _), a, b) == Op(a, b)
Gen(A(_), k) == ENABLED A(k)
Wrap(B(_), k) == Gen(B, k)
Both(F(_), v) == F(v) /\ F(v + 1)
Twice(A(_), k) == A(k) \/ A(k + 1)
Capture(F(_), v) == \E z \in {v} : F(z)
Next == Twice(Step, 2)
TwoParams == Fold(Add, x, 1) <= 4
NestedPass == x < 3 => Wrap(Step, 3)
UsedTwice == Both(Lt, x)
LetOperator == LET G(v) == v < 4 IN Apply(G, x)
CaptureOk == Capture(LAMBDA z : z < 4, x)
FromLib == ApplyLib(Lt, x)
====
