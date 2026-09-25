---- MODULE QuantFair ----
EXTENDS Naturals
VARIABLE pc
Procs == {1, 2}
Init == pc = [p \in Procs |-> "a"]
Loop(p) == p = 1 /\ pc' = [pc EXCEPT ![1] = IF pc[1] = "a" THEN "b" ELSE "a"]
Fin(p) == p = 2 /\ pc[2] = "a" /\ pc' = [pc EXCEPT ![2] = "done"]
Next == \E p \in Procs : Loop(p) \/ Fin(p)
SpecQN == Init /\ [][Next]_pc /\ WF_pc(Next)
SpecQE == Init /\ [][Next]_pc /\ \A p \in Procs : WF_pc(Loop(p) \/ Fin(p))

PropC32 == <>(pc[2] = "done")
====
