---- MODULE c3po_asteroid_field ----
EXTENDS Naturals

VARIABLES falcon, shields, hyperdrive, pursuit, hiding

Init ==
    /\ falcon = "flying"
    /\ shields = 3
    /\ hyperdrive = "broken"
    /\ pursuit = "active"
    /\ hiding = FALSE

AsteroidImpact ==
    /\ falcon = "flying"
    /\ hiding = FALSE
    /\ shields > 0
    /\ shields' = shields - 1
    /\ UNCHANGED <<falcon, hyperdrive, pursuit, hiding>>

AsteroidDestroysShip ==
    /\ falcon = "flying"
    /\ hiding = FALSE
    /\ shields = 0
    /\ falcon' = "destroyed"
    /\ UNCHANGED <<shields, hyperdrive, pursuit, hiding>>

HideInCave ==
    /\ falcon = "flying"
    /\ hiding = FALSE
    /\ hiding' = TRUE
    /\ pursuit' = "lost_them"
    /\ UNCHANGED <<falcon, shields, hyperdrive>>

SlugAwakens ==
    /\ hiding = TRUE
    /\ falcon = "flying"
    /\ hiding' = FALSE
    /\ pursuit' = "active"
    /\ UNCHANGED <<falcon, shields, hyperdrive>>

R2FixesHyperdrive ==
    /\ falcon = "flying"
    /\ hyperdrive = "broken"
    /\ hyperdrive' = "fixed"
    /\ UNCHANGED <<falcon, shields, pursuit, hiding>>

JumpToHyperspace ==
    /\ falcon = "flying"
    /\ hyperdrive = "fixed"
    /\ falcon' = "escaped"
    /\ pursuit' = "escaped"
    /\ UNCHANGED <<shields, hyperdrive, hiding>>

TIEFighterAttack ==
    /\ falcon = "flying"
    /\ pursuit = "active"
    /\ hiding = FALSE
    /\ shields > 0
    /\ shields' = shields - 1
    /\ UNCHANGED <<falcon, hyperdrive, pursuit, hiding>>

Next ==
    \/ AsteroidImpact
    \/ AsteroidDestroysShip
    \/ HideInCave
    \/ SlugAwakens
    \/ R2FixesHyperdrive
    \/ JumpToHyperspace
    \/ TIEFighterAttack

InvNeverTellMeTheOdds ==
    falcon /= "destroyed"

ShieldsHolding ==
    shields > 0

Escaped ==
    falcon = "escaped"

HyperdriveLive ==
    hyperdrive = "fixed"

====
