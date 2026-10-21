---- MODULE FILib ----
EXTENDS Naturals
CONSTANT Base
fact[n \in Nat] == IF n = 0 THEN 1 ELSE n * fact[n - 1]
scaled[n \in Nat] == IF n = 0 THEN Base ELSE n * scaled[n - 1]
pair[a \in 0..2, b \in 0..2] == a + b
====
