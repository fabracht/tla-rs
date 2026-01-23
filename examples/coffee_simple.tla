VARIABLE can

Can == [black : 0..3, white : 0..3]

Init == can \in {c \in Can : c.black + c.white \in 1..3}

PickSameColorBlack ==
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

Next ==
    \/ PickSameColorBlack
    \/ UNCHANGED can

TypeInvariant == can \in Can
