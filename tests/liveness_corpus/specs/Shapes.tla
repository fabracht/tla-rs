---- MODULE Shapes ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Step == x < 2 /\ x' = x + 1 /\ y' = y
Next == Step \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars /\ WF_vars(Step)
SpecT == Init /\ [][Next]_vars /\ WF_<<x, y>>(Step)
SpecNF == Init /\ [][Next]_vars
S == {1, 2}
Safe(i) == [](x # i)
Reach(i) == <>(x = i)
PSafeQ == \A i \in {7, 8} : Safe(i)
PSafeBad == Safe(2)
PReachQ == \A i \in S : Reach(i)
PReach3 == Reach(3)
PNotEv == ~<>(x = 9)
PNotEvBad == ~<>(x = 2)
PNotBox == ~[](x < 2)
PNotBoxEv == ~[]<>(x = 1)
PLet == LET k == 2 IN <>(x = k)
PLetOp == LET R(i) == <>(x = i) IN R(3)
PIf == IF 1 = 1 THEN [](x < 1) ELSE TRUE
PIfElse == IF 1 = 2 THEN [](x < 1) ELSE <>(x = 2)
PGuardBad == \A i \in S : (i = 1 => <>(x = 9))
PGuardOk == \A i \in S : (i = 1 => <>(x = 2))
PBoxBox == [][](x < 5)
PEvEv == <><>(x = 2)
PTuple == \A <<i, j>> \in S \X S : [](x # i + j + 10)
PTupleBad == \A <<i, j>> \in S \X S : [](x # i + j)
PSubParen == [][x' >= x]_(x)
PSubTupleBad == [][y' = y + 1]_<<x>>
PSubRecordOk == [][x' = x + 1]_[a |-> x]
PSubExprBad == [][x' = x]_(x + y)
PEnabledInit == ENABLED Step
PEnabledAct == [][ENABLED Step]_x
PEnabledActBad == [][ENABLED Step]_y
PStateImpl == (x = 0) => [](x < 2)
====
