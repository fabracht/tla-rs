---- MODULE bitwise_and ----
EXTENDS Bits

VARIABLES x

Init == x = 0

Next == x' = x + 1 /\ x < 10

TypeOK ==
    /\ 5 & 3 = 1
    /\ 7 & 4 = 4
    /\ 15 & 8 = 8
    /\ 6 & 2 = 2
    /\ 0 & 255 = 0

====
