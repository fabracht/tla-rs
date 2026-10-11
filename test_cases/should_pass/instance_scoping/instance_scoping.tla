---- MODULE instance_scoping ----
EXTENDS Naturals, ISibling1, ISibling2
VARIABLE x
Three == 3
N == 4
F(a) == a * 100
Add(a, b) == a + b
INSTANCE IOuter WITH K <- Three
INSTANCE IImplicit
Init == x = 0
Next == UNCHANGED x
InvSibling == Mx(1) = 2 /\ Hundred = 100
InvOwnScope == UsesInner = 2 /\ F(1) = 100
InvParam == Offset(2) = 7
InvFold == Fold(Add, 1, 2) = 3 /\ Fold(LAMBDA a, b : a * b, 3, 4) = 12
InvWith == Scaled = 6
InvImplicit == Implicit = 5
InvRecursive == Fact(4) = 24
InvNested == UsesNested = 50
====
