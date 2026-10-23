---- MODULE function_instance ----
EXTENDS Naturals
VARIABLE x
tbl == [i \in 1..3 |-> i]
I == INSTANCE FILib WITH Base <- 1, T <- tbl
P(k) == INSTANCE FILib WITH Base <- k, T <- tbl
InvCount[i \in 1..2] == i * 2
Init == x = 0
Next == x < 2 /\ LET up[n \in 0..3] == IF n = 0 THEN 1 ELSE up[n - 1] + 1 IN x' = up[x]
InvInstance == I!fact[4] = 24 /\ I!pair[1, 2] = 3 /\ P(2)!scaled[3] = 12
InvLocal == InvCount[2] = 4 /\ I!Get(2) = 2 /\ P(1)!Get(3) = 3
InvWhole == DOMAIN I!pair = (0..2) \X (0..2) /\ I!pair = [a, b \in 0..2 |-> a + b]
====
