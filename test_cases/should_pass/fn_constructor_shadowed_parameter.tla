---- MODULE fn_constructor_shadowed_parameter ----
EXTENDS Integers, Sequences, TLC
Jobs == {"j1", "j2"}
CP == << ("refs" :> <<10>>), ("refs" :> <<20>>) >>
Trace == << [job |-> "j1", refs |-> <<1, 2>>], [job |-> "j2", refs |-> <<3>>] >>
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}
Refs(seq) == [j \in Jobs |-> SeqToSet(seq[1]["refs"])]
CheckpointRefs(seq) ==
    [j \in Jobs |->
        LET matches == {i \in 1..Len(seq) : seq[i]["job"] = j}
        IN IF matches = {}
           THEN {}
           ELSE SeqToSet(seq[CHOOSE i \in matches : TRUE]["refs"])]
Twice(j) == 2 * j
First(S) == LET e == CHOOSE x \in S : TRUE IN IF S = {} THEN 0 ELSE e
VARIABLE x
Init == x = 0
Next == x' = x
InvRefs == Refs(CP) = [j \in Jobs |-> {10}]
InvCheckpointRefs == CheckpointRefs(Trace) = [j1 |-> {1, 2}, j2 |-> {3}]
InvBoundArgument == [j \in 1..3 |-> Twice(j + 1)] = [j \in 1..3 |-> 2 * j + 2]
InvLazyBinding == [e \in {1, 2} |-> First(IF e = 1 THEN {} ELSE {e * 5})] = (1 :> 0 @@ 2 :> 10)
====
