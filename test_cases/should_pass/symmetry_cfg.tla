---- MODULE symmetry_cfg ----
EXTENDS Naturals

CONSTANT Proc

VARIABLE votes

Init == votes = [p \in Proc |-> 0]

Next == \E p \in Proc :
    /\ votes[p] < 2
    /\ votes' = [votes EXCEPT ![p] = @ + 1]

Inv == \A p \in Proc : votes[p] <= 2

====
