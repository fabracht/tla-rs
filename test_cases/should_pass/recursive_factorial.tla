VARIABLES n, result

RECURSIVE Factorial(_)
Factorial(x) == IF x = 0 THEN 1 ELSE x * Factorial(x - 1)

Init == n = 3 /\ result = Factorial(n)

Next == UNCHANGED <<n, result>>

Inv == result = 6
