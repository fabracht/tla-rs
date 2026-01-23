---- MODULE is_finite_set ----
EXTENDS FiniteSets

VARIABLES x

Init == x = {1, 2, 3}

Next == x' = x

Inv == IsFiniteSet(x) /\ IsFiniteSet({}) /\ IsFiniteSet(SUBSET {1,2})
====
