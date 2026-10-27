---- MODULE instance_shadowed_definition_action ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
I == INSTANCE SAct WITH y <- x
Init == x = 0
Next == I!MNext
Spec == Init /\ [][Next]_x /\ WF_x(Next)
InvRange == x \in {0, 9}
Live == <>I!Reached
====
