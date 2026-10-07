---- MODULE definition_parse_error ----
EXTENDS Integers
CONSTANT Limit
VARIABLE x
Bad == [a/b |-> 1]
Derived == Bad.a
Init == x = 0
Next == x < Limit /\ x' = x + 1
Small == x <= Limit
====
