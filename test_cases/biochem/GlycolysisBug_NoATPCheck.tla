---- MODULE GlycolysisBug_NoATPCheck ----
EXTENDS Naturals

CONSTANTS InitGlucose, InitATP, InitNAD, MaxPool

VARIABLES glucose, f16bp, g3p, bpg, pep, pyruvate, atp, adp, nad, nadh

vars == <<glucose, f16bp, g3p, bpg, pep, pyruvate, atp, adp, nad, nadh>>

Init ==
    /\ glucose = InitGlucose
    /\ f16bp = 0
    /\ g3p = 0
    /\ bpg = 0
    /\ pep = 0
    /\ pyruvate = 0
    /\ atp = InitATP
    /\ adp = 0
    /\ nad = InitNAD
    /\ nadh = 0

Phosphorylation ==
    /\ glucose >= 1
    /\ f16bp + 1 <= MaxPool
    /\ adp + 2 <= MaxPool
    /\ glucose' = glucose - 1
    /\ f16bp' = f16bp + 1
    /\ atp' = atp - 2
    /\ adp' = adp + 2
    /\ UNCHANGED <<g3p, bpg, pep, pyruvate, nad, nadh>>

Split ==
    /\ f16bp >= 1
    /\ g3p + 2 <= MaxPool
    /\ f16bp' = f16bp - 1
    /\ g3p' = g3p + 2
    /\ UNCHANGED <<glucose, bpg, pep, pyruvate, atp, adp, nad, nadh>>

Oxidation ==
    /\ g3p >= 1
    /\ nad >= 1
    /\ bpg + 1 <= MaxPool
    /\ nadh + 1 <= MaxPool
    /\ g3p' = g3p - 1
    /\ bpg' = bpg + 1
    /\ nad' = nad - 1
    /\ nadh' = nadh + 1
    /\ UNCHANGED <<glucose, f16bp, pep, pyruvate, atp, adp>>

FirstSubstrateLevelP ==
    /\ bpg >= 1
    /\ adp >= 1
    /\ pep + 1 <= MaxPool
    /\ atp + 1 <= MaxPool
    /\ bpg' = bpg - 1
    /\ pep' = pep + 1
    /\ adp' = adp - 1
    /\ atp' = atp + 1
    /\ UNCHANGED <<glucose, f16bp, g3p, pyruvate, nad, nadh>>

SecondSubstrateLevelP ==
    /\ pep >= 1
    /\ adp >= 1
    /\ pyruvate + 1 <= MaxPool
    /\ atp + 1 <= MaxPool
    /\ pep' = pep - 1
    /\ pyruvate' = pyruvate + 1
    /\ adp' = adp - 1
    /\ atp' = atp + 1
    /\ UNCHANGED <<glucose, f16bp, g3p, bpg, nad, nadh>>

Next ==
    \/ Phosphorylation
    \/ Split
    \/ Oxidation
    \/ FirstSubstrateLevelP
    \/ SecondSubstrateLevelP

TypeOK ==
    /\ glucose >= 0 /\ glucose <= MaxPool
    /\ f16bp >= 0 /\ f16bp <= MaxPool
    /\ g3p >= 0 /\ g3p <= MaxPool
    /\ bpg >= 0 /\ bpg <= MaxPool
    /\ pep >= 0 /\ pep <= MaxPool
    /\ pyruvate >= 0 /\ pyruvate <= MaxPool
    /\ atp >= 0 /\ atp <= MaxPool
    /\ adp >= 0 /\ adp <= MaxPool
    /\ nad >= 0 /\ nad <= MaxPool
    /\ nadh >= 0 /\ nadh <= MaxPool

InvATPNonNegative == atp >= 0

InvNADNonNegative == nad >= 0

InvATPConservation == atp + adp = InitATP

InvNADConservation == nad + nadh = InitNAD

InvCarbonConservation ==
    (glucose * 6) + (f16bp * 6) + (g3p * 3) + (bpg * 3) + (pep * 3) + (pyruvate * 3) = InitGlucose * 6

ATPPositive == atp > 0

NADAvailable == nad > 0

PathwayComplete == glucose = 0 /\ f16bp = 0 /\ g3p = 0 /\ bpg = 0 /\ pep = 0

EnergyPayoff == atp > InitATP

Deadlocked ==
    /\ ~(glucose >= 1 /\ f16bp + 1 <= MaxPool /\ adp + 2 <= MaxPool)
    /\ ~(f16bp >= 1 /\ g3p + 2 <= MaxPool)
    /\ ~(g3p >= 1 /\ nad >= 1 /\ bpg + 1 <= MaxPool /\ nadh + 1 <= MaxPool)
    /\ ~(bpg >= 1 /\ adp >= 1 /\ pep + 1 <= MaxPool /\ atp + 1 <= MaxPool)
    /\ ~(pep >= 1 /\ adp >= 1 /\ pyruvate + 1 <= MaxPool /\ atp + 1 <= MaxPool)

====
