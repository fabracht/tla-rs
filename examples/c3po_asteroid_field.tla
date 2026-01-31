---- MODULE c3po_asteroid_field ----
EXTENDS Naturals

CONSTANT Asteroids

VARIABLES falcon, shields, ties, slug

Init ==
    /\ falcon = "flying"
    /\ shields = 10
    /\ ties = 4
    /\ slug = "asleep"

AsteroidStrike(dmg) ==
    /\ falcon = "flying"
    /\ shields >= dmg
    /\ shields' = shields - dmg
    /\ UNCHANGED <<falcon, ties, slug>>

AsteroidDestroysShip(dmg) ==
    /\ falcon = "flying"
    /\ shields < dmg
    /\ falcon' = "destroyed"
    /\ UNCHANGED <<shields, ties, slug>>

AsteroidDestroysTIE ==
    /\ falcon \in {"flying", "hiding"}
    /\ ties > 0
    /\ ties' = ties - 1
    /\ UNCHANGED <<falcon, shields, slug>>

TIEFighterAttack ==
    /\ falcon = "flying"
    /\ ties > 0
    /\ shields > 0
    /\ shields' = shields - 1
    /\ UNCHANGED <<falcon, ties, slug>>

HideInCave ==
    /\ falcon = "flying"
    /\ slug = "asleep"
    /\ falcon' = "hiding"
    /\ UNCHANGED <<shields, ties, slug>>

MynockDamage ==
    /\ falcon = "hiding"
    /\ slug = "asleep"
    /\ shields > 0
    /\ shields' = shields - 1
    /\ slug' = "disturbed"
    /\ UNCHANGED <<falcon, ties>>

ThisIsNoCave ==
    /\ falcon = "hiding"
    /\ slug = "disturbed"
    /\ slug' = "attacking"
    /\ UNCHANGED <<falcon, shields, ties>>

EscapeSlugMouth ==
    /\ falcon = "hiding"
    /\ slug = "attacking"
    /\ shields > 2
    /\ falcon' = "flying"
    /\ shields' = shields - 2
    /\ slug' = "escaped"
    /\ UNCHANGED <<ties>>

SlugEatsShip ==
    /\ falcon = "hiding"
    /\ slug = "attacking"
    /\ shields <= 2
    /\ falcon' = "destroyed"
    /\ UNCHANGED <<shields, ties, slug>>

AttachToStarDestroyer ==
    /\ falcon = "flying"
    /\ ties = 0
    /\ falcon' = "attached"
    /\ UNCHANGED <<shields, ties, slug>>

FloatAwayWithGarbage ==
    /\ falcon = "attached"
    /\ falcon' = "escaped"
    /\ UNCHANGED <<shields, ties, slug>>

Next ==
    \/ \E dmg \in Asteroids : AsteroidStrike(dmg)
    \/ \E dmg \in Asteroids : AsteroidDestroysShip(dmg)
    \/ AsteroidDestroysTIE
    \/ TIEFighterAttack
    \/ HideInCave
    \/ MynockDamage
    \/ ThisIsNoCave
    \/ EscapeSlugMouth
    \/ SlugEatsShip
    \/ AttachToStarDestroyer
    \/ FloatAwayWithGarbage

InvNeverTellMeTheOdds ==
    falcon /= "destroyed"

ShieldsHolding ==
    shields > 0

Escaped ==
    falcon = "escaped"

====
