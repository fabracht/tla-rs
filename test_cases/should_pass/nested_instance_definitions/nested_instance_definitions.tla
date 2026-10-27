---- MODULE nested_instance_definitions ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
I == INSTANCE CtM
P == INSTANCE Pm
Init == x = 0
Next == x < 1 /\ x' = x + 1
InvDefinition == I!Read = 5
InvPath == P!Read = 3
====
