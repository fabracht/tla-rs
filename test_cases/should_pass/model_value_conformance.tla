---- MODULE model_value_conformance ----
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANT Node, n1, n2

VARIABLE x
Init == x = 0
Next == x' = 1 - x

fmv == [n \in {n1,n2} |-> "idle"]
fstr == [n \in {"n1","n2"} |-> "idle"]
recN == [n1 |-> "idle", n2 |-> "idle"]
gmv == (n1 :> "idle" @@ n2 :> "idle")

InvE02 == ~(n1 = 1)
InvE03 == ~(n1 = TRUE)
InvP01 == n1 = n1
InvP02 == ~(n1 = n2)
InvP03 == n1 # n2
InvP04 == ~(n1 = "n1")
InvP05 == Cardinality({n1,n2}) = 2
InvP06 == Cardinality({n1,n2} \cup {"n1","n2"}) = 4
InvP07 == Cardinality({n1,"n1"}) = 2
InvP08 == ~("n1" \in {n1,n2})
InvP09 == ~(n1 \in {"n1","n2"})
InvP10 == ({n1} \cap {"n1"}) = {}
InvP13 == DOMAIN fmv = {n1,n2}
InvP14 == fmv[n1] = "idle"
InvP16 == fmv = (n1 :> "idle" @@ n2 :> "idle")
InvP20 == fmv \in [{n1,n2} -> {"idle","busy"}]
InvP21 == [{n1,n2} -> {1}] = {(n1 :> 1 @@ n2 :> 1)}
InvP22 == Cardinality([{n1,n2} -> {1,2}]) = 4
InvP23 == [a |-> n1] = [a |-> n1]
InvP24 == ~([a |-> n1] = [a |-> n2])
InvP26 == <<n1,n2>>[1] = n1
InvP29 == Cardinality(Node) = 2
InvP30 == Cardinality({n1,1}) = 2
InvP33 == IsFiniteSet({n1,n2})
InvP36 == ToString(n1) = "n1"

====
