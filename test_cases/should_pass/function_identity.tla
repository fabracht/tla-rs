---- MODULE function_identity ----

EXTENDS Naturals, Sequences, FiniteSets

VARIABLE x

Init == x = 0
Next == x' = 1 - x

rec  == [a |-> 1, b |-> 2]
frec == ("a" :> 1 @@ "b" :> 2)
tup  == <<10, 20>>
ftup == (1 :> 10 @@ 2 :> 20)
emptyfcn == [i \in {} |-> 0]

InvRecEqFn   == rec = frec
InvTupEqFn   == tup = ftup
InvEmptyEq   == <<>> = emptyfcn
InvCardRec   == Cardinality({rec, frec}) = 1
InvCardTup   == Cardinality({tup, ftup}) = 1
InvCardEmpty == Cardinality({<<>>, emptyfcn}) = 1

InvRecNeqTup == rec # tup

InvRecInFnSet  == rec \in [{"a", "b"} -> Nat]
InvFrecInFnSet == frec \in [{"a", "b"} -> Nat]
InvTupInFnSet  == tup \in [1 .. 2 -> Nat]
InvFtupInFnSet == ftup \in [1 .. 2 -> Nat]
InvDomMismatch == rec \notin [{"a"} -> Nat]

InvRecInRecSet  == rec \in [a: Nat, b: Nat]
InvFrecInRecSet == frec \in [a: Nat, b: Nat]

InvWitness == \E f \in [{"a", "b"} -> {1, 2}] : f = rec
InvFilter  == {f \in [{"a", "b"} -> {1, 2}] : f = rec} = {rec}
InvSubset  == {rec} \subseteq [{"a", "b"} -> {1, 2}]

InvFrecField == frec.a = 1
InvFrecApply == frec["a"] = rec.a
InvDomFrec   == DOMAIN frec = {"a", "b"}
InvDomFtup   == DOMAIN ftup = {1, 2}

InvSeqOps == Len(ftup) = 2 /\ Head(ftup) = 10 /\ Append(ftup, 30) = <<10, 20, 30>>
InvSeqSet == ftup \in Seq(Nat)

InvExceptFrec == [frec EXCEPT !.a = 9] = [a |-> 9, b |-> 2]
InvExceptFtup == [ftup EXCEPT ![1] = 9] = <<9, 20>>

====
