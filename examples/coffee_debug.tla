VARIABLE can

Can == {0, 1}

Init == can = 0

PickAction ==
    /\ can = 0
    /\ can' = 1

Next ==
    \/ PickAction
    \/ UNCHANGED can

TypeInvariant == can \in Can
