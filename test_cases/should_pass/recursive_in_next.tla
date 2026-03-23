VARIABLES x

RECURSIVE Double(_)
Double(n) == IF n = 0 THEN 0 ELSE 2 + Double(n - 1)

Init == x = 0
Next == IF x < 5 THEN x' = Double(x + 1) ELSE UNCHANGED x
Inv == x >= 0 /\ x <= 10
