---- MODULE model_value_state_space ----

CONSTANT Node

VARIABLE s

Init == s = {}

Next == \E v \in (Node \cup {"n1", "n2"}) : s' = s \cup {v}

TypeOK == s \subseteq (Node \cup {"n1", "n2"})

====
