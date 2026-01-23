CONSTANT N

ASSUME N > 0 /\ N <= 10

VARIABLES count

Init == count = 0

Next == count < N /\ count' = count + 1

Inv == count <= N
