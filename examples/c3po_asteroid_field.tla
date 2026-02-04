---- MODULE c3po_asteroid_field ----
EXTENDS Naturals

CONSTANT Density

VARIABLES falcon, shields, hull, ties, slug, systems

Init ==
    /\ falcon = "flying"
    /\ shields = 10
    /\ hull = 5
    /\ ties = 4
    /\ slug = "asleep"
    /\ systems = [sensors |-> "ok", weapons |-> "ok", engines |-> "ok"]

TakeDamage(dmg, newFalcon) ==
    LET absorbed == IF shields >= dmg THEN dmg ELSE shields
        overflow == dmg - absorbed
        stress == dmg \div 3
        hullDmg == overflow + stress
    IN IF hull > hullDmg
       THEN /\ shields' = shields - absorbed
            /\ hull' = hull - hullDmg
            /\ falcon' = newFalcon
       ELSE /\ falcon' = "destroyed"
            /\ UNCHANGED <<shields, hull>>

Fly(dmg) ==
    /\ falcon = "flying"
    /\ TakeDamage(dmg, "flying")
    /\ UNCHANGED <<ties, slug, systems>>

TIEFighterAttack(dmg) ==
    /\ falcon = "flying"
    /\ ties > 0
    /\ TakeDamage(dmg + 1, "flying")
    /\ UNCHANGED <<ties, slug, systems>>

AsteroidDestroysTIE ==
    /\ falcon \in {"flying", "hiding"}
    /\ ties > 0
    /\ ties' = ties - 1
    /\ UNCHANGED <<falcon, shields, hull, slug, systems>>

SensorDamage(dmg) ==
    /\ falcon = "flying"
    /\ systems.sensors = "ok"
    /\ TakeDamage(dmg, "flying")
    /\ systems' = [systems EXCEPT !.sensors = "damaged"]
    /\ UNCHANGED <<ties, slug>>

EngineDamage(dmg) ==
    /\ falcon = "flying"
    /\ systems.engines = "ok"
    /\ TakeDamage(dmg, "flying")
    /\ systems' = [systems EXCEPT !.engines = "damaged"]
    /\ UNCHANGED <<ties, slug>>

WeaponsDamage(dmg) ==
    /\ falcon = "flying"
    /\ systems.weapons = "ok"
    /\ TakeDamage(dmg, "flying")
    /\ systems' = [systems EXCEPT !.weapons = "damaged"]
    /\ UNCHANGED <<ties, slug>>

BlindFly(dmg) ==
    /\ falcon = "flying"
    /\ systems.sensors = "damaged"
    /\ TakeDamage(dmg + 2, "flying")
    /\ UNCHANGED <<ties, slug, systems>>

SluggishDodge(dmg) ==
    /\ falcon = "flying"
    /\ systems.engines = "damaged"
    /\ TakeDamage(dmg + 1, "flying")
    /\ UNCHANGED <<ties, slug, systems>>

HideInCave(dmg) ==
    /\ falcon = "flying"
    /\ slug = "asleep"
    /\ systems.sensors = "ok"
    /\ TakeDamage(dmg, "hiding")
    /\ UNCHANGED <<ties, slug, systems>>

MynockDamage(sys) ==
    /\ falcon = "hiding"
    /\ slug = "asleep"
    /\ shields > 0
    /\ hull > 0
    /\ shields' = shields - 1
    /\ hull' = hull - 1
    /\ slug' = "disturbed"
    /\ systems' = [systems EXCEPT ![sys] = "damaged"]
    /\ UNCHANGED <<falcon, ties>>

ThisIsNoCave ==
    /\ falcon = "hiding"
    /\ slug = "disturbed"
    /\ slug' = "attacking"
    /\ UNCHANGED <<falcon, shields, hull, ties, systems>>

EscapeSlugMouth ==
    /\ falcon = "hiding"
    /\ slug = "attacking"
    /\ systems.engines = "ok"
    /\ shields > 2
    /\ hull > 1
    /\ falcon' = "flying"
    /\ shields' = shields - 2
    /\ hull' = hull - 1
    /\ slug' = "escaped"
    /\ UNCHANGED <<ties, systems>>

SlugEatsShip ==
    /\ falcon = "hiding"
    /\ slug = "attacking"
    /\ (shields <= 2 \/ hull <= 1 \/ systems.engines = "damaged")
    /\ falcon' = "destroyed"
    /\ UNCHANGED <<shields, hull, ties, slug, systems>>

AttachToStarDestroyer(dmg) ==
    /\ falcon = "flying"
    /\ ties = 0
    /\ systems.engines = "ok"
    /\ TakeDamage(dmg, "attached")
    /\ UNCHANGED <<ties, slug, systems>>

FloatAwayWithGarbage ==
    /\ falcon = "attached"
    /\ falcon' = "escaped"
    /\ UNCHANGED <<shields, hull, ties, slug, systems>>

Next ==
    \/ \E dmg \in 1..Density:
        \/ Fly(dmg)
        \/ TIEFighterAttack(dmg)
        \/ HideInCave(dmg)
        \/ AttachToStarDestroyer(dmg)
        \/ SensorDamage(dmg)
        \/ EngineDamage(dmg)
        \/ WeaponsDamage(dmg)
        \/ BlindFly(dmg)
        \/ SluggishDodge(dmg)
    \/ AsteroidDestroysTIE
    \/ \E sys \in {"sensors", "engines", "weapons"}: MynockDamage(sys)
    \/ ThisIsNoCave
    \/ EscapeSlugMouth
    \/ SlugEatsShip
    \/ FloatAwayWithGarbage

InvNeverTellMeTheOdds ==
    falcon /= "destroyed"

Escaped ==
    falcon = "escaped"

====
