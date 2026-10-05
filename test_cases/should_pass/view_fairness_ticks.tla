---- MODULE view_fairness_ticks ----
EXTENDS Integers
VARIABLES x, aux
vars == <<x, aux>>
Init == x = 0 /\ aux = 0
Inc == x < 3 /\ x' = x + 1 /\ UNCHANGED aux
Tick == x = 3 /\ aux' = aux + 1 /\ UNCHANGED x
Next == Inc \/ Tick
Spec == Init /\ [][Next]_vars /\ WF_vars(Inc) /\ WF_vars(Tick)
Back == []<>(x = 0)
Stays == <>[](x = 3)
Project == x
Ticks == []<><<Tick>>_vars
====
