---- MODULE SFSub ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Go1 == x = 0 /\ x' = 1
Go2 == x = 0 /\ x' = 2
Back == x \in {1, 2} /\ x' = 0
A == x = 1 /\ x' = 5
Next == Go1 \/ Go2 \/ Back \/ A \/ UNCHANGED x
SpecSF == Init /\ [][Next]_x /\ SF_x(A) /\ WF_x(Back)

PropC31 == <>(x = 5)
====
