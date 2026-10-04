---- MODULE PrimedCalls ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
I == INSTANCE PrimedInner WITH v <- x
Init == x = 0 /\ y = 0
RECURSIVE Below(_)
Below(n) == IF n = 0 THEN x >= 0 ELSE Below(n - 1) /\ x < 2
RECURSIVE Sum(_)
Sum(n) == IF n = 0 THEN x ELSE n + Sum(n - 1)
Step == x < 3 /\ x' = x + 1 /\ y' = y
Spec == Init /\ [][Step]_vars
RecOp == Below(1)
RecOpPrimed == [][x' = 2 => ~RecOp']_vars
RecPrimedViolated == [][x' = 2 => Below(1)']_vars
SumPrimed == [][Sum(2)' = Sum(2) + 1]_vars
InstancePrimed == [][x' = 2 => ~I!Small(2)']_vars
InstancePrimedViolated == [][x' = 2 => I!Small(2)']_vars
GuardNext == x < 3 /\ x' = x + 1 /\ Below(1)' /\ y' = y
SpecGuard == Init /\ [][GuardNext]_vars
ValueNext == x < 3 /\ x' = x + 1 /\ y' = Sum(1)'
SpecValue == Init /\ [][ValueNext]_vars
InvYIsSum == y = 0 \/ y = x + 1
====
