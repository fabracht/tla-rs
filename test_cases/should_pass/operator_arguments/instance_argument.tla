---- MODULE instance_argument ----
EXTENDS Naturals
VARIABLES x
I == INSTANCE LibI
Init == x = 0
Next == x' = x
Apply(F(_), v) == F(v)
Inv == Apply(I!Lt, x)
====
