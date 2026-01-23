CONSTANT MAX

VARIABLES x, y, z

Init == x = 0 /\ y = 0 /\ z = 0

Next ==
    \/ (x < MAX /\ x' = x + 1 /\ y' = y /\ z' = z)
    \/ (y < MAX /\ x' = x /\ y' = y + 1 /\ z' = z)
    \/ (z < MAX /\ x' = x /\ y' = y /\ z' = z + 1)

Inv == x <= MAX /\ y <= MAX /\ z <= MAX
