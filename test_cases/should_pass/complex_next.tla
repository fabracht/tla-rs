VARIABLES x, y

Init == x = 0 /\ y = 0

Inc(v) == v + 1

Next ==
    \/ (x < 2 /\ x' = Inc(x) /\ y' = y)
    \/ (y < 2 /\ y' = Inc(y) /\ x' = x)

InvX == x <= 2
InvY == y <= 2
