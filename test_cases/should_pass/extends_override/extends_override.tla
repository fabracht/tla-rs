---- MODULE extends_override ----
EXTENDS Defs

Limit == 3

VARIABLES x

Init == x = 0
Next == x' = IF x < Limit THEN x + 1 ELSE x
Inv == x <= 3
====
