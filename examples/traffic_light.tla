VARIABLES light, count

Init == light = 0 /\ count = 0

Next ==
    \/ (light = 0 /\ light' = 1 /\ count' = count)
    \/ (light = 1 /\ light' = 2 /\ count' = count)
    \/ (light = 2 /\ light' = 0 /\ count' = count + 1)

Inv == light \in {0, 1, 2}

InvCount == count <= 3
