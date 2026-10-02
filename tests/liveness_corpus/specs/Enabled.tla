---- MODULE Enabled ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Step == x < 2 /\ x' = x + 1
Reset == x = 2 /\ x' = 0
Jump == x' = 7
Keep == x' = x
Next == Step
SpecF == Init /\ [][Next]_x /\ WF_x(Step)
SpecNF == Init /\ [][Next]_x
SpecJump == Init /\ [][Next]_x /\ WF_x(Jump)
NeverTwo == <>(x = 2)
SpecCycle == Init /\ [][Step \/ Reset]_x /\ WF_x(Step \/ Reset)
StableDisabled == <>[](~ENABLED Step)
JumpEventuallyDisabled == <>(~ENABLED Jump)
AngleKeep == []<>(~ENABLED <<Keep>>_x)
AngleStep == []<>(~ENABLED <<Step>>_x)
EnabledImplies == [](ENABLED Step => <>(x = 2))
EnabledLeads == ENABLED Step ~> ~ENABLED Step
EnabledInQuant == \A v \in {0, 1} : [](x = v => <>~ENABLED Step)
ResetOften == []<>ENABLED Reset
WFStep == WF_x(Step)
SFStep == SF_x(Step)
WFProp == WF_x(Step) /\ <>(x = 2)
NotWF == ~WF_x(Step)
WFTuple == WF_<<x>>(Step)
WFJump == WF_x(Jump)
WFKeep == WF_x(Keep)
HandWF == <>[](ENABLED <<Step>>_x) => []<><<Step>>_x
ASpec == Init /\ [][Next]_x /\ WF_x(Step)
SFReset == SF_x(Reset)
WFOrBox == WF_x(Step) \/ [](x = 0)
SFImpliesWF == SF_x(Step) => WF_x(Step)
====
