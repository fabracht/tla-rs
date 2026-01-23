CONSTANT MAX

VARIABLES count

Init == count = 0

Next == count' = count + 1 /\ count < MAX

Inv == count <= MAX
