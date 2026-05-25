---- MODULE tuple_binding_quantifier ----
EXTENDS Naturals

VARIABLE x

Pairs == {<<1, 2>>, <<2, 3>>, <<3, 4>>}

Init == x = 0

Next ==
    /\ \E <<a, b>> \in Pairs : x' = a + b
    /\ x' < 100

Inv ==
    /\ \A <<a, b>> \in Pairs : a < b
    /\ \E <<a, b>> \in Pairs : a + b = 3
    /\ x \in {0, 3, 5, 7}

====
