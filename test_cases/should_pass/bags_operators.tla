---- MODULE bags_operators ----
EXTENDS Bags

VARIABLES x

bag1 == (1 :> 2) @@ (2 :> 3)
bag2 == (1 :> 1) @@ (3 :> 1)

Init ==
    /\ x = 0

Next ==
    /\ x < 1
    /\ x' = x + 1

InvIsABag == IsABag(bag1)

InvBagToSet == BagToSet(bag1) = {1, 2}

InvSetToBag == SetToBag({1, 2}) = (1 :> 1) @@ (2 :> 1)

InvBagIn == BagIn(1, bag1)

InvBagNotIn == ~BagIn(5, bag1)

InvEmptyBag == BagCardinality(EmptyBag) = 0

InvBagAdd == (bag1 \oplus bag2) = (1 :> 3) @@ (2 :> 3) @@ (3 :> 1)

InvBagSub == (bag1 \ominus bag2) = (1 :> 1) @@ (2 :> 3)

InvSqSubseteq == (1 :> 1) \sqsubseteq bag1

InvBagCardinality == BagCardinality(bag1) = 5

InvCopiesIn == CopiesIn(1, bag1) = 2

InvCopiesInZero == CopiesIn(99, bag1) = 0

====
