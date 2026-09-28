---- MODULE Guards ----
EXTENDS Naturals, TLC
CONSTANT N
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A == y = 0 /\ y' = 1 /\ x' = x
B == y = 1 /\ x = 0 /\ x' = 1 /\ y' = y
C == x = 1 /\ x' = 2 /\ y' = y
Next == A \/ B \/ C
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
GetLevel1 == TLCGet("level") = 1 => [](x < 1)
GetLevel1Ev == TLCGet("level") = 1 => <>(x = 9)
GetDistinct == TLCGet("distinct") = 1 => <>(x = 9)
GetIf == IF TLCGet("level") = 1 THEN [](x < 1) ELSE TRUE
GetLevelGt == TLCGet("level") > 1 => [](x < 1)
DomY == \A i \in {y} : [](x # i + 1)
S == {y}
DomDef == \A i \in S : [](x # i + 1)
NegIf == ~(IF N = 2 THEN [](x < 0) ELSE [](x < 10))
NegIfBad == ~(IF N = 2 THEN [](x < 0) ELSE [](x < 1))
LetOp == LET F(v) == v + 1 IN <>(x = F(1))
LetOpBad == LET F(v) == v + 1 IN [](x < F(1))
LetOpAct == LET F(v) == v + 1 IN [][x' = F(x) \/ x' = x]_x
LetOpLeads == LET F(v) == v + 1 IN (x = 0) ~> (x = F(1))
LetOpQ == LET F(v) == v + 1 IN \A i \in 0..1 : <>(x = F(i))
P(i) == LET F(j) == j + i IN <>(x = F(1))
LetOpNested == P(1)
====
