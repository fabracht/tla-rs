---- MODULE ExistsProps ----
EXTENDS Naturals
VARIABLE pc
P == {1, 2}
Init == pc = [p \in P |-> "a"]
Go(p) == pc[p] = "a" /\ pc' = [pc EXCEPT ![p] = "b"]
Back(p) == pc[p] = "b" /\ pc' = [pc EXCEPT ![p] = "a"]
Next == \E p \in P : Go(p) \/ Back(p)
S == Init /\ [][Next]_pc /\ \A p \in P : WF_pc(Go(p) \/ Back(p))
ExSE == \E p \in P : <>[](pc[p] = "a")
ExLT == \E p \in P : (pc[p] = "a") ~> (pc[p] = "c")
ExBoxImp == \E p \in P : [](pc[p] = "a" => <>(pc[p] = "c"))
AllSE == \A p \in P : <>[](pc[p] = "a")
====
