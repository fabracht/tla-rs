---- MODULE seq_index ----
EXTENDS Naturals, Sequences
VARIABLES s, n
vars == <<s, n>>
Init == s = <<0, 0>> /\ n = 0
Next == (s' \in {<<1,1>>, <<2,2>>} /\ n' = s'[1] + 100) \/ UNCHANGED vars
Inv == n # 102
====
