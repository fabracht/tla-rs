---- MODULE extends_parse_error ----
EXTENDS Broken

VARIABLES x

Init == x = 0
Next == x' = x
Inv == x = 0
====
