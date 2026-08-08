---- MODULE tlc_conformance_functions ----
EXTENDS Naturals, Integers, Sequences, FiniteSets

VARIABLE x
Init == x = 0
Next == x' = 1 - x

rec == [a |-> 1, b |-> 2]
frec == (("a" :> 1) @@ ("b" :> 2))
tup == <<10, 20>>
ftup == ((1 :> 10) @@ (2 :> 20))
emptyfn == [i \in {} |-> 0]
noncontig == ((1 :> "a") @@ (3 :> "b"))
zerobase == ((0 :> "z") @@ (1 :> "o"))
mixdom == ((1 :> "i") @@ ("k" :> "s"))
one == <<7>>
onerec == [a |-> 7]
fone == (1 :> 7)
frecone == ("a" :> 7)

InvE01 == rec = frec
InvE02 == tup = ftup
InvE03 == one = fone
InvE04 == onerec = frecone
InvE05 == <<>> = emptyfn
InvE09 == noncontig = [i \in {1,3} |-> IF i = 1 THEN "a" ELSE "b"]
InvE10 == zerobase = [i \in {0,1} |-> IF i = 0 THEN "z" ELSE "o"]
InvD10 == DOMAIN rec = DOMAIN frec
InvD11 == DOMAIN tup = DOMAIN ftup
InvX11 == [rec EXCEPT !["a"] = 9] = [frec EXCEPT !["a"] = 9]
InvX12 == [tup EXCEPT ![1] = 9] = [ftup EXCEPT ![1] = 9]
InvF01 == rec \in [{"a","b"} -> {1,2}]
InvF02 == frec \in [{"a","b"} -> {1,2}]
InvF03 == tup \in [{1,2} -> {10,20}]
InvF04 == ftup \in [{1,2} -> {10,20}]
InvF08 == emptyfn \in [{} -> {1}]
InvF09 == <<>> \in [{} -> {1}]
InvF11 == noncontig \in [{1,3} -> {"a","b"}]
InvR01 == rec \in [a: {1}, b: {2}]
InvR02 == frec \in [a: {1}, b: {2}]
InvR03 == onerec \in [a: {7}]
InvR04 == frecone \in [a: {7}]
InvS01 == tup \in Seq({10,20})
InvS02 == ftup \in Seq({10,20})
InvS03 == one \in Seq({7})
InvS04 == fone \in Seq({7})
InvS05 == <<>> \in Seq({1})
InvS06 == emptyfn \in Seq({1})
InvQ15 == Tail(ftup) = <<20>>
InvQ16 == Append(ftup, 30) = <<10,20,30>>
InvN04 == <<rec>> = <<frec>>
InvN05 == [k |-> tup] = [k |-> ftup]
InvN06 == {rec} = {frec}
InvU01 == {rec} \subseteq {frec}
InvU02 == {frec} \subseteq {rec}
InvM01 == rec \in {frec}
InvM02 == ftup \in {tup}
InvM03 == {rec, frec} = {rec}
InvM13 == \E f \in [{"a","b"} -> {1,2}] : f = rec
InvM14 == \E f \in {frec} : f = rec
InvG03 == [i \in 1..2 |-> i*10] = tup
InvG04 == [i \in 1..2 |-> i*10] = ftup
InvG07 == [i \in {"a","b"} |-> IF i = "a" THEN 1 ELSE 2] = rec
InvG09 == <<10>> \o <<20>> = ftup
InvG16 == rec \in [{"a","b"} -> Nat]
InvG17 == frec \in [{"a","b"} -> Nat]
InvG18 == tup \in [1..2 -> Nat]
InvG19 == ftup \in [1..2 -> Nat]
InvG20 == onerec \in [a: Nat]
InvG21 == frecone \in [a: Nat]
InvG22 == {<<>>} = {emptyfn}
InvG33 == IsFiniteSet({rec, frec})
InvG37 == <<rec, frec>>[1] = <<rec, frec>>[2]
InvG38 == fone \in Seq(Nat)
InvG40 == {rec} \cup {frec} = {rec}

====
