---- MODULE less_than_before_digit ----
EXTENDS Integers
VARIABLES x, y
Val == x<3
Init == x = 0 /\ y = FALSE
Next == x' = (x + 1) % 4 /\ y' = Val
Inv == y # TRUE
====
