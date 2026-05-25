---- MODULE tuple_binding_comprehension ----
EXTENDS Naturals, FiniteSets

VARIABLE x

Pairs == {<<1, 2>>, <<2, 3>>, <<3, 4>>, <<5, 5>>}

OrderedPairs == {<<a, b>> \in Pairs : a < b}

Sums == {a + b : <<a, b>> \in Pairs}

PairFn == [<<a, b>> \in Pairs |-> a * b]

Init == x = 0

Next == \/ x' = Cardinality(OrderedPairs)
        \/ x' = Cardinality(Sums)
        \/ x' = PairFn[<<2, 3>>]

Inv ==
    /\ OrderedPairs = {<<1, 2>>, <<2, 3>>, <<3, 4>>}
    /\ Sums = {3, 5, 7, 10}
    /\ PairFn[<<3, 4>>] = 12
    /\ x \in {0, 3, 4, 6}

====
