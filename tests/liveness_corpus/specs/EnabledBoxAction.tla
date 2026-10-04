---- MODULE EnabledBoxAction ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x < 2 /\ x' = x + 1 /\ y' = y
Spec == Init /\ [][Inc]_vars /\ WF_vars(Inc)
SpecBox == Init /\ [][[Inc]_vars]_vars
EnabledBox == []<>ENABLED [Inc]_vars
NotEnabledBox == <>~ENABLED [Inc]_vars
StepProp == [][[x' > x]_x]_vars
StepPropBad == [][[x' > x + 1]_(x + y)]_vars
Reach == <>(x = 2)
====
