---- MODULE five_chain ----
EXTENDS Naturals
VARIABLES a, b, c, d, e
vars == <<a, b, c, d, e>>
Init == a=0 /\ b=0 /\ c=0 /\ d=0 /\ e=0
Next == (a'=1 /\ b'=a'+1 /\ c'=b'+1 /\ d'=c'+1 /\ e'=d'+1) \/ UNCHANGED vars
Inv == e # 5
====
