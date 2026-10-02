---- MODULE Enabled3 ----
EXTENDS Naturals, FiniteSets
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x < 2 /\ x' = x + 1 /\ y' = y
Spec == Init /\ [][Inc]_vars /\ WF_vars(Inc)
SpecNF == Init /\ [][Inc]_vars
En(a) == ENABLED a
LetAction == []<>(LET a == Inc IN ~ENABLED a)
LetActionBox == [](LET a == Inc IN ENABLED a)
ArgAction == []<>~En(Inc)
ArgActionBox == [](x < 2 => En(Inc))
EquivEnabled == [](ENABLED Inc <=> x < 2)
CaseEnabled == <>[](CASE x = 2 -> ~ENABLED Inc [] OTHER -> FALSE)
SetEnabled == <>[]({v \in {1} : ENABLED Inc} = {})
CardEnabled == []<>(Cardinality({v \in {1} : ENABLED Inc}) = 0)
====
