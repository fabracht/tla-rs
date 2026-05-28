---- MODULE TimeIntegrity ----
EXTENDS Integers

CONSTANTS MaxTime, Tol, MinPlausible

VARIABLES
    realTime,
    wallClock,
    bootTime,
    floor,
    prevSample,
    firstBoot,
    tampered,
    ntpSynced

vars ==
    <<realTime, wallClock, bootTime, floor, prevSample, firstBoot, tampered, ntpSynced>>

NoSample == -1

AbsDiff(a, b) == IF a >= b THEN a - b ELSE b - a
Min2(a, b) == IF a < b THEN a ELSE b
Max2(a, b) == IF a > b THEN a ELSE b

TrackedTime == Min2(floor + bootTime, MaxTime)
RefNow == Max2(TrackedTime, wallClock)

Init ==
    /\ realTime = 0
    /\ wallClock = 0
    /\ bootTime = 0
    /\ floor = 0
    /\ prevSample = NoSample
    /\ firstBoot = TRUE
    /\ tampered = FALSE
    /\ ntpSynced = FALSE

Tick ==
    /\ realTime < MaxTime
    /\ realTime' = realTime + 1
    /\ bootTime' = Min2(bootTime + 1, MaxTime)
    /\ wallClock' = IF ntpSynced
                    THEN Min2(realTime + 1, MaxTime)
                    ELSE Min2(wallClock + 1, MaxTime)
    /\ UNCHANGED <<floor, prevSample, firstBoot, tampered, ntpSynced>>

TamperWallClock ==
    /\ \E v \in 0..MaxTime : wallClock' = v
    /\ UNCHANGED <<realTime, bootTime, floor, prevSample, firstBoot, tampered, ntpSynced>>

BootCheck ==
    /\ \/ /\ wallClock < MinPlausible
          /\ UNCHANGED <<floor, prevSample, firstBoot, tampered>>
       \/ /\ wallClock >= MinPlausible
          /\ firstBoot
          /\ floor' = wallClock
          /\ prevSample' = wallClock
          /\ firstBoot' = FALSE
          /\ UNCHANGED tampered
       \/ /\ wallClock >= MinPlausible
          /\ ~firstBoot
          /\ prevSample' = wallClock
          /\ tampered' = IF AbsDiff(wallClock, floor) > Tol THEN TRUE ELSE tampered
          /\ UNCHANGED <<floor, firstBoot>>
    /\ UNCHANGED <<realTime, wallClock, bootTime, ntpSynced>>

Cadence ==
    /\ \/ /\ wallClock < MinPlausible
          /\ UNCHANGED <<floor, prevSample, firstBoot, tampered>>
       \/ /\ wallClock >= MinPlausible
          /\ firstBoot
          /\ floor' = wallClock
          /\ prevSample' = wallClock
          /\ firstBoot' = FALSE
          /\ UNCHANGED tampered
       \/ /\ wallClock >= MinPlausible
          /\ ~firstBoot
          /\ floor' = Min2(Max2(floor + bootTime, wallClock), MaxTime)
          /\ tampered' = IF prevSample # NoSample /\ AbsDiff(prevSample, wallClock) > Tol
                         THEN TRUE
                         ELSE tampered
          /\ prevSample' = wallClock
          /\ UNCHANGED firstBoot
    /\ UNCHANGED <<realTime, wallClock, bootTime, ntpSynced>>

NTPSync ==
    /\ wallClock' = realTime
    /\ ntpSynced' = TRUE
    /\ \/ /\ realTime < MinPlausible
          /\ UNCHANGED <<floor, prevSample, firstBoot, tampered>>
       \/ /\ realTime >= MinPlausible
          /\ firstBoot
          /\ floor' = realTime
          /\ prevSample' = realTime
          /\ firstBoot' = FALSE
          /\ UNCHANGED tampered
       \/ /\ realTime >= MinPlausible
          /\ ~firstBoot
          /\ floor' = Min2(Max2(floor + bootTime, realTime), MaxTime)
          /\ prevSample' = realTime
          /\ tampered' = IF prevSample # NoSample /\ AbsDiff(prevSample, realTime) > Tol
                         THEN TRUE
                         ELSE IF tampered /\ (floor > realTime + Tol)
                              THEN TRUE
                              ELSE FALSE
          /\ UNCHANGED firstBoot
    /\ UNCHANGED <<realTime, bootTime>>

NTPLose ==
    /\ ntpSynced
    /\ ntpSynced' = FALSE
    /\ UNCHANGED <<realTime, wallClock, bootTime, floor, prevSample, firstBoot, tampered>>

Reboot ==
    /\ bootTime' = 0
    /\ ntpSynced' = FALSE
    /\ prevSample' = NoSample
    /\ \E v \in 0..MaxTime : wallClock' = v
    /\ UNCHANGED <<realTime, floor, firstBoot, tampered>>

Next ==
    \/ Tick
    \/ TamperWallClock
    \/ BootCheck
    \/ Cadence
    \/ NTPSync
    \/ NTPLose
    \/ Reboot

TypeOK ==
    /\ realTime \in 0..MaxTime
    /\ wallClock \in 0..MaxTime
    /\ bootTime \in 0..MaxTime
    /\ floor \in 0..MaxTime
    /\ prevSample \in {NoSample} \cup (0..MaxTime)
    /\ firstBoot \in BOOLEAN
    /\ tampered \in BOOLEAN
    /\ ntpSynced \in BOOLEAN

InvSeeded == (~tampered) \/ (~firstBoot)
====
