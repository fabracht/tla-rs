---- MODULE symbolic_nat ----
EXTENDS Integers, FiniteSets

VARIABLES x

Init == x = 0
Next == x' = x

InvMemberNat == 5 \in Nat
InvNonMemberNat == ~(-3 \in Nat)
InvMemberInt == -3 \in Int
InvBeyondBoundNat == 150 \in Nat
InvBeyondBoundInt == -150 \in Int
InvSetMinus == 4 \in (Nat \ {0})
InvUnionLeft == -1 \in (Nat \cup {-1})
InvUnionRight == 5 \in (Nat \cup {-1})
InvCartesian == <<3, "a">> \in (Nat \X {"a"})
InvCartesian3Flat == <<3, "a", 4>> \in (Nat \X {"a"} \X Nat)
InvCartesian3FlatNotNested == ~(<<3, "a", 4>> \in (Nat \X ({"a"} \X Nat)))
InvCartesian3Nested == <<3, <<"a", 4>>>> \in (Nat \X ({"a"} \X Nat))
InvSubseteq == {1, 2, 3} \subseteq Nat
InvBoundedQuantifier == \A n \in 0..3 : n \in Nat
InvNatInfinite == ~IsFiniteSet(Nat)
InvIntInfinite == ~IsFiniteSet(Int)
====
