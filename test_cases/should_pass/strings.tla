---- MODULE strings ----
EXTENDS Integers, Sequences, TLC
VARIABLES x, name
Quoted == "a\"b"
Trace == "work" :> <<"[\"4916d32b\",\"work-1\"]">>
Init == x = 0 /\ name = "a\\b"
Next == x < 2 /\ x' = x + 1 /\ name' = Quoted
TypeOK == /\ x \in Nat
          /\ name \in STRING
          /\ Quoted \in STRING
Escapes == /\ Quoted /= "ab"
           /\ Trace["work"][1] = "[\"4916d32b\",\"work-1\"]"
           /\ name \in {"a\\b", "a\"b"}
====
