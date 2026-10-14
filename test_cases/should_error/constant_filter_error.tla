---- MODULE constant_filter_error ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == 3 \in {n \in 0..3 : 6 \div (n - 1) > 0}
====
