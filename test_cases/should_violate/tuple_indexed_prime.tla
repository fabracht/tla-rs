---- MODULE tuple_indexed_prime ----

EXTENDS Naturals

VARIABLE x

Init == x = <<1, 2>>

Next == x'[1] = 5 /\ x'[2] = x[2]

Inv == x[1] # 5

====
