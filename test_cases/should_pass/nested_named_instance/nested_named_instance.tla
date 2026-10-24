---- MODULE nested_named_instance ----
EXTENDS Naturals
VARIABLES x, w
I1 == INSTANCE NNMid WITH y <- x, C <- 5
I2 == INSTANCE NNMid WITH y <- w, C <- 7
INSTANCE NNUnnamed WITH u <- x, D <- 0
Init == x = 0 /\ w = 10
Next == x < 2 /\ x' = x + 1 /\ w' = w
InvSeparate == I1!Read = x + 1 /\ I2!Read = w + 1
InvInherited == I1!ReadC = 5 /\ I2!ReadC = 7
InvUnnamed == Twice = 2 * x
====
