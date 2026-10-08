---- MODULE recursive_fn_under_operator ----
EXTENDS Integers
Factorial == LET f[n \in 0..4] == IF n = 0 THEN 1 ELSE n * f[n - 1] IN f
LetFactorial == LET f[n \in 0..4] == LET r == f[n - 1] IN IF n = 0 THEN 1 ELSE n * r IN f[4]
Fact(k) == LET f[n \in 0..k] == IF n = 0 THEN 1 ELSE n * f[n - 1] IN f[k]
Fib == LET f[n \in 0..20] == IF n < 2 THEN n ELSE f[n - 1] + 1 * f[n - 2] IN f[20]
PowerOfTwo == LET f[m \in 0..2] == IF m = 0 THEN 1 ELSE 2 * f[m - 1] IN f[2]
Nested == LET f[n \in 0..3] == IF n = 0 THEN 0 ELSE PowerOfTwo + 10 * n IN f
VARIABLE x
Init == x = 0
Next == x' = x
InvFactorial == Factorial = [n \in 0..4 |-> CASE n = 0 -> 1 [] n = 1 -> 1 [] n = 2 -> 2 [] n = 3 -> 6 [] n = 4 -> 24]
InvLetFactorial == LetFactorial = 24
InvOperator == Fact(5) = 120
InvFib == Fib = 6765
InvNested == Nested = [n \in 0..3 |-> IF n = 0 THEN 0 ELSE 4 + 10 * n]
====
