---- MODULE log_matching ----
EXTENDS Integers
CONSTANTS Server, Index
Nil == [term |-> 0, leader |-> "none"]
VARIABLE engineLog
Init == engineLog = [s \in Server |-> [i \in Index |-> Nil]]
Write(s, i) == /\ engineLog[s][i] = Nil
               /\ IF i = 1 THEN TRUE ELSE engineLog[s][i - 1] /= Nil
               /\ engineLog' = [engineLog EXCEPT ![s][i] = [term |-> 1, leader |-> "n1"]]
Next == \E s \in Server, i \in Index : Write(s, i)
LogMatching ==
    \A s, t \in Server, i \in Index :
      /\ engineLog[s][i] /= Nil
      /\ engineLog[t][i] /= Nil
      /\ engineLog[s][i].term = engineLog[t][i].term
      /\ engineLog[s][i].leader = engineLog[t][i].leader
      => \A j \in 1..i :
           /\ engineLog[s][j] /= Nil
           /\ engineLog[t][j] /= Nil
====
