---- MODULE extends_missing_module ----
EXTENDS NotThere

VARIABLES x

Init == x = 0
Next == x' = x
Inv == x = 0
====
