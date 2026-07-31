---- MODULE fn_merge_precedence ----

EXTENDS Naturals

VARIABLE x

Init == x = 0
Next == x' = 1 - x

InvDomain   == DOMAIN (1 :> 10 @@ 2 :> 20) = {1, 2}
InvApply1   == (1 :> 10 @@ 2 :> 20)[1] = 10
InvApply2   == (1 :> 10 @@ 2 :> 20)[2] = 20
InvThree    == ("a" :> 1 @@ "b" :> 2 @@ "c" :> 3)["c"] = 3
InvAssoc    == (1 :> 10 @@ 2 :> 20) = (1 :> 10 @@ (2 :> 20))
InvTighter  == (1 :> 2 + 3) = (1 :> 5)
InvRangeRhs == ("k" :> 1 .. 3) = ("k" :> {1, 2, 3})

====
