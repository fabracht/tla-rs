---- MODULE transitive_closure ----

VARIABLES step

R == {<<1, 2>>, <<2, 3>>, <<3, 4>>}

TransitiveClosure == R^+

ReflexiveClosure == R^*

Init ==
    /\ step = 0

Next ==
    /\ step < 3
    /\ step' = step + 1

TypeOK ==
    /\ <<1, 2>> \in TransitiveClosure
    /\ <<1, 3>> \in TransitiveClosure
    /\ <<1, 4>> \in TransitiveClosure
    /\ <<2, 3>> \in TransitiveClosure
    /\ <<2, 4>> \in TransitiveClosure
    /\ <<3, 4>> \in TransitiveClosure
    /\ <<1, 1>> \in ReflexiveClosure
    /\ <<2, 2>> \in ReflexiveClosure

====
