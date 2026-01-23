VARIABLES x, y

Init == x = 2 /\ y = 2^10

Next == UNCHANGED <<x, y>>

Inv == y = 1024
