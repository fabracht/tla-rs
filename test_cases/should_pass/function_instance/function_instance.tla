---- MODULE function_instance ----
EXTENDS Naturals
VARIABLE x
I == INSTANCE FILib WITH Base <- 1
P(k) == INSTANCE FILib WITH Base <- k
InvCount[i \in 1..2] == i * 2
Init == x = 0
Next == x < 2 /\ LET up[n \in 0..3] == IF n = 0 THEN 1 ELSE up[n - 1] + 1 IN x' = up[x]
InvInstance == I!fact[4] = 24 /\ I!pair[1, 2] = 3 /\ P(2)!scaled[3] = 12
InvLocal == InvCount[2] = 4
====
