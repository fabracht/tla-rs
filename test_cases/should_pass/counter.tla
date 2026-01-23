VARIABLES count

Init == count = 0

Next == count' = count + 1 /\ count < 3

Inv == count <= 3
