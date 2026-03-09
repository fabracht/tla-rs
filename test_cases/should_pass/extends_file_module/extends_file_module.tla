---- MODULE extends_file_module ----
EXTENDS Helpers

VARIABLES x

Init == x = 0
Next == x' = Clamp(x + 1, 0, 3)
Inv == x \in 0..3
====
