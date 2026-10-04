---- MODULE SymFairIdle ----
EXTENDS Naturals, TLC
CONSTANT P
VARIABLES pc, lock
vars == <<pc, lock>>
Init == pc = [p \in P |-> "idle"] /\ lock = "none"
Try(p) == pc[p] = "idle" /\ pc' = [pc EXCEPT ![p] = "wait"] /\ UNCHANGED lock
Enter(p) == pc[p] = "wait" /\ lock = "none" /\ pc' = [pc EXCEPT ![p] = "cs"] /\ lock' = p
Exit(p) == pc[p] = "cs" /\ pc' = [pc EXCEPT ![p] = "idle"] /\ lock' = "none"
Next == \E p \in P : Try(p) \/ Enter(p) \/ Exit(p)
Sym == Permutations(P)
Spec == Init /\ [][Next]_vars /\ (\A p \in P : WF_vars(Try(p))) /\ (\A p \in P : SF_vars(Enter(p))) /\ (\A p \in P : SF_vars(Exit(p)))
IdleOften == \A p \in P : []<>(pc[p] = "idle")
====
