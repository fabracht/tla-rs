---- MODULE OperatorArgument ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x < 2 /\ x' = x + 1 /\ y' = y
Spec == Init /\ [][Inc]_vars /\ WF_vars(Inc)
Step(k) == x < k /\ x' = x + 1 /\ y' = y
Gen(A(_), k) == ENABLED A(k)
EventuallyDisabled == <>[]~Gen(Step, 2)
EventuallyDisabledLambda == <>[]~Gen(LAMBDA k : x < k /\ x' = x + 1 /\ y' = y, 2)
EventuallyEnabled == <>[]Gen(Step, 2)
====
