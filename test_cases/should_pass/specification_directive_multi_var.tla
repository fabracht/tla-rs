---- MODULE specification_directive_multi_var ----
LOCAL INSTANCE Integers

VARIABLES number, toggle

vars == <<number, toggle>>

Numbers == {22, 23}
NumberMax == 23
NumberMin == 22

Init ==
  /\ number \in Numbers
  /\ toggle \in BOOLEAN

NumberIncrease ==
  /\ number < NumberMax
  /\ number' = number + 1
  /\ UNCHANGED toggle

NumberDecrease ==
  /\ number > NumberMin
  /\ number' = number - 1
  /\ UNCHANGED toggle

Toggle ==
  /\ toggle' = ~toggle
  /\ UNCHANGED number

Next ==
  \/ NumberIncrease
  \/ NumberDecrease
  \/ Toggle

Spec ==
  /\ Init
  /\ [][Next]_vars

TypeOK ==
  /\ number \in Numbers
  /\ toggle \in BOOLEAN

====
