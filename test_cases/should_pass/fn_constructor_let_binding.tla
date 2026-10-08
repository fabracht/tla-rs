---- MODULE fn_constructor_let_binding ----
EXTENDS Naturals
Sum(limit) ==
    LET f[i \in 1..limit] == LET r == f[i - 1] IN IF i = 1 THEN 1 ELSE i + r
    IN f[limit]
Guarded ==
    LET f[i \in 1..3] == LET r == IF i > 0 THEN f[i - 1] ELSE 0 IN IF i = 1 THEN 1 ELSE i + r
    IN f
VARIABLE x
Init == x = 0
Next == x' = x
InvUnusedRecursiveBinding == Sum(3) = 6
InvDomainUnchanged == DOMAIN Guarded = 1..3
InvParameterizedLet == [j \in 1..3 |-> LET g(y) == y + 1 IN g(j)] = [j \in 1..3 |-> j + 1]
InvBindingNotCaptured == [j \in 1..3 |-> LET j2 == j + 1 IN \E j \in {7} : j2 = j + 1] = [j \in 1..3 |-> FALSE]
====
