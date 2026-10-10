---- MODULE instance_module_missing ----
EXTENDS IUsesMissing
VARIABLE x
Init == x = 0
Next == UNCHANGED x
InvOk == Four = 4
====
