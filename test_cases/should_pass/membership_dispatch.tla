---- MODULE membership_dispatch ----
EXTENDS Naturals, Sequences

VARIABLE x

Init == x = 0

A == x = 0 /\ {{1}, {2}} \in SUBSET SUBSET {1, 2} /\ x' = 1
B == x = 0 /\ <<<<1>>, <<2>>>> \in Seq(Seq({1, 2})) /\ x' = 2
C == x = 0 /\ [a |-> <<1>>] \in [a: Seq({1, 2})] /\ x' = 3

Next == A \/ B \/ C \/ (x # 0 /\ UNCHANGED x)

InvEnabledAgrees ==
    /\ (ENABLED A) = (x = 0)
    /\ (ENABLED B) = (x = 0)
    /\ (ENABLED C) = (x = 0)

====
