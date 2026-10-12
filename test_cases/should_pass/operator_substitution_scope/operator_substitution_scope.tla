---- MODULE operator_substitution_scope ----
EXTENDS Integers, FiniteSets, Sequences
VARIABLE x
INSTANCE OSShared
Own == INSTANCE OSOwn
Shared == INSTANCE OSShared
Init == x = 0
MCInit == x = 1
Lim == 99
MCLim == 5
MCVal == 1
MCCard(S) == 42
Short(S) == {<<>>} \cup {<<e>> : e \in S}
Apply(F(_), v) == F(v)
MCApply(F(_), v) == F(v) + 10
Inc(n) == n + 1
Next == x < 20 /\ x' = Apply(Inc, x)
InvInit == x \in {1, 12, 23}
InvOwnInit == Own!Init = (x = 7)
InvBound == Own!HasLim
InvSharedVal == Shared!UsesVal = 2
InvUnnamedVal == UsesVal = 2
InvSeq == Shared!SeqSmall = 1
InvCard == Cardinality({1}) = 42
InvNat == -1 \in Nat
====
