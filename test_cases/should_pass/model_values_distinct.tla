---- MODULE model_values_distinct ----

EXTENDS Naturals, FiniteSets

CONSTANT Node

VARIABLE x

fmv  == [n \in Node |-> "idle"]
fstr == [n \in {"n1", "n2"} |-> "idle"]

Init == x = 0
Next == x' = 1 - x

InvCard     == Cardinality(Node \cup {"n1", "n2"}) = 4
InvDistinct == fmv # fstr
InvNotIn    == "n1" \notin Node
InvDomain   == DOMAIN fmv # DOMAIN fstr

====
