---- MODULE FILib ----
EXTENDS Naturals
CONSTANT Base, T
tbl == [i \in 1..3 |-> 100]
Get(i) == T[i]
fact[n \in Nat] == IF n = 0 THEN 1 ELSE n * fact[n - 1]
scaled[n \in Nat] == IF n = 0 THEN Base ELSE n * scaled[n - 1]
pair[a \in 0..2, b \in 0..2] == a + b
====
