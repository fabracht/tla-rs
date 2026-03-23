VARIABLES x

RECURSIVE Id(_)
Id(n) == IF n = 0 THEN 0 ELSE 1 + Id(n - 1)

Init == x \in {0, 1}
Next == x' = Id(1 - x)
Inv == x \in {0, 1}
