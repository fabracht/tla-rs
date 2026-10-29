---- MODULE unchanged_expression ----
EXTENDS Naturals
VARIABLES y, q, pair, a, b
I == INSTANCE UX WITH y <- pair[1], z <- q
Keep(v) == UNCHANGED v
Init == y = 0 /\ q = 0 /\ pair = <<0>> /\ a = 0 /\ b = 0
Next == \/ pair' = <<pair[1] + 1>> /\ UNCHANGED <<y, a, b>> /\ I!Bump
        \/ a < 2 /\ a' = a + 1 /\ Keep(<<b>>) /\ UNCHANGED <<y, q, pair>>
Inv == b = 0 /\ q = 0 /\ pair = <<0>>
====
