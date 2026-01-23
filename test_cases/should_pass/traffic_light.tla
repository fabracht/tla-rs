VARIABLES light

Init == light \in {"red", "green", "yellow"}

Next ==
    \/ (light = "red" /\ light' = "green")
    \/ (light = "green" /\ light' = "yellow")
    \/ (light = "yellow" /\ light' = "red")

TypeInv == light \in {"red", "green", "yellow"}
