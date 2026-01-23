VARIABLE can

Init == can = [black |-> 0, white |-> 1]

PickAction ==
    /\ can.white < 5
    /\ can' = [can EXCEPT !.white = @ + 1]

Next ==
    \/ PickAction
    \/ UNCHANGED can

TypeInvariant == can.white <= 5
