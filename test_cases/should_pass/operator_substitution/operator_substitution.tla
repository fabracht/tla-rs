---- MODULE operator_substitution ----
EXTENDS OSBase
MCInit == x = 1 /\ s = <<>>
MCBump(n) == n + 2
Short(S) == {<<>>} \cup {<<e>> : e \in S}
MCLimit == 5
SmallNat == 0 .. 3
InvInit == x # 0
InvBump == x % 2 = 1
InvSeq == Len(s) <= 1
====
