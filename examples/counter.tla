VARIABLES count

Init == count = 0

Next == count' = count + 1 /\ count < 5

Inv == count <= 5
