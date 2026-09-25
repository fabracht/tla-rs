---- MODULE FairProp ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Step == x < 2 /\ x' = x + 1
Next == Step
Fairness == WF_x(Step)
SpecNamed == Init /\ [][Next]_x /\ Fairness
Spec == Init /\ [][Next]_x
FairSpec == Init /\ [][Next]_x /\ WF_x(Step)
Reach == <>(x = 2)
L1 == <>(x = 2)
L2 == []<>(x = 1)
Both == L1 /\ L2
WProp == WF_x(Step) /\ <>(x = 2)
Imp == (x = 0) => <>(x = 2)
NotEv == ~<>(x = 1)
====
