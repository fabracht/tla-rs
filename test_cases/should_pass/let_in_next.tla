VARIABLES count

Init == count = 0

Next ==
    LET limit == 3
    IN count < limit /\ count' = count + 1

Inv == count <= 3
