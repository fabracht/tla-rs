---- MODULE recursive_dotdot ----
EXTENDS Naturals

VARIABLE x

Sum(limit) ==
  LET f[i \in 1..limit] ==
    IF i = 1 THEN 1 ELSE i + f[i - 1]
  IN f[limit]

Init == x = 0

Next == x' = Sum(3)

Inv == x \in {0, 6}

====
