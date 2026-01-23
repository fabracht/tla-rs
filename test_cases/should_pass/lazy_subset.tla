---- MODULE lazy_subset ----
EXTENDS Naturals, FiniteSets

VARIABLE x

LargeSet == 0..30

Init == x = {}

Next == \E n \in LargeSet:
    /\ Cardinality(x) < 3
    /\ n \notin x
    /\ x' = x \cup {n}

TypeOK == x \in SUBSET LargeSet

Inv == Cardinality(x) <= 3

====
