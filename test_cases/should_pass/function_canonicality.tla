---- MODULE function_canonicality ----
EXTENDS Naturals, Sequences, FiniteSets

VARIABLE x
Init == x = 0
Next == x' = 1 - x

Canon(f) == f = [i \in DOMAIN f |-> f[i]]

c01 == (1 :> 9)
c02 == (1 :> 9 @@ 2 :> 5)
c03 == ("a" :> 1 @@ "b" :> 2)
c04 == [<<1,2>> EXCEPT ![1] = 9]
c05 == [<<1,2>> EXCEPT ![1] = 9, ![2] = 8]
c06 == [<<1,2>> EXCEPT ![1] = 9, ![1] = @ + 1]
c07 == [[a |-> 1] EXCEPT !.a = 9]
c08 == [(1 :> 9 @@ 3 :> 5) EXCEPT ![1] = 7]
c09 == [<< <<0,0>> >> EXCEPT ![1][1] = 9]
c10 == [<< <<0,0>> >> EXCEPT ![1] = <<7,8>>, ![1][2] = 9]
c11 == [[r |-> <<1,2>>] EXCEPT !.r[1] = 9]
c12 == Append(<<1,2>>, 3)
c13 == Tail(<<1,2,3>>)
c14 == SubSeq(<<1,2,3>>, 2, 3)
c15 == <<1>> \o <<2>>
c16 == [i \in 1..3 |-> i * 2]
c17 == [i \in {"a","b"} |-> 1]
c18 == CHOOSE f \in [1..2 -> {5}] : TRUE
c19 == [i \in {} |-> 0]
c20 == [<<1,2,3>> EXCEPT ![1] = 9, ![2] = @ * 2, ![3] = @ + 100]

InvC01 == Canon(c01)
InvC02 == Canon(c02)
InvC03 == Canon(c03)
InvC04 == Canon(c04)
InvC05 == Canon(c05)
InvC06 == Canon(c06)
InvC07 == Canon(c07)
InvC08 == Canon(c08)
InvC09 == Canon(c09)
InvC10 == Canon(c10)
InvC11 == Canon(c11)
InvC12 == Canon(c12)
InvC13 == Canon(c13)
InvC14 == Canon(c14)
InvC15 == Canon(c15)
InvC16 == Canon(c16)
InvC17 == Canon(c17)
InvC18 == Canon(c18)
InvC19 == Canon(c19)
InvC20 == Canon(c20)

InvDedup == Cardinality({c05, <<9,8>>}) = 1
InvDedup2 == Cardinality({c02, <<9,5>>}) = 1
InvDedup3 == Cardinality({c16, <<2,4,6>>}) = 1

====
