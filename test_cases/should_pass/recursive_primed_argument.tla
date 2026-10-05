---- MODULE recursive_primed_argument ----
EXTENDS Naturals
VARIABLES x
RECURSIVE AllSmall(_)
AllSmall(s) == IF s = {} THEN TRUE ELSE LET e == CHOOSE e \in s : TRUE IN e < 3 /\ AllSmall(s \ {e})
Init == x = {}
Next == x' \in {{1}, {1,2}} /\ AllSmall(x')
====
