---- MODULE LetLevel ----
EXTENDS KLib
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x < 2 /\ x' = x + 1 /\ y' = y
Spec == Init /\ [][Inc]_vars /\ WF_vars(Inc)
En(a) == ENABLED a
Lt3(v) == v < 2
ViaLet == [](LET a == Inc IN ENABLED a)
ViaCall == []En(Inc)
LetUnused == [](LET a == Inc IN x < 2)
LetHolds == [](LET a == Inc IN x <= 2)
LetState == [](LET a == x + 1 IN a < 3)
DirectEn == [](ENABLED Inc)
EnLet == [](ENABLED (LET a == Inc IN a))
CallUnused == []K(Inc)
CallUnusedHolds == []Ks(Inc)
CallState == []Lt3(x)
ParamLet == [](LET F(v) == v' = v IN x < 2)
LetInEnabledCall == [](ENABLED K(Inc))
TopLet == LET a == Inc IN x > 0
TopLetHolds == LET a == Inc IN x = 0
====
