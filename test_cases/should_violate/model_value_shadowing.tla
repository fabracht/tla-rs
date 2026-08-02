---- MODULE model_value_shadowing ----

EXTENDS Naturals

CONSTANT Proc

VARIABLE x

Init == x = 0

Next == x' = x + 1 /\ x < Threshold

Threshold == 3

Inv == x < 3

====
