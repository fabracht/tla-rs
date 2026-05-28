# Time-integrity alert state machine

## 1. Pre-init guard prevents a first-boot false positive ✓

Identical events on a dead-RTC boot (wallClock starts at 0). With the guard, BootCheck defers below MinPlausible and the first plausible NTP seeds cleanly. Without it, BootCheck seeds prevSample=0, so the first NTP looks like a huge forward jump and raises a false alert that only self-clears on the next sync.

Scenario:

```
action: BootCheck
action: Tick
action: Tick
action: Tick
action: NTPSync
action: Tick
action: NTPSync
```

**Variant `guard`** — spec `TimeIntegrity.tla`, config `TimeIntegrity.cfg`

- ✓ `all: tampered = FALSE`

**Variant `noguard`** — spec `TimeIntegrity.tla`, config `TimeIntegrity.cfg`, constants MinPlausible=0

- ✓ `step 5: tampered = TRUE`
- ✓ `final: tampered = FALSE`

## 2. Honest forward jump: detected, blocks one NTP, then clears ✓

After a clean seed (floor=3), wallClock jumps forward to 9. The stale-floor check at BootCheck raises the alert (step 6). The first NTP still sees a jump vs prevSample so it stays raised (step 7); the next stable NTP clears it (step 9).

Scenario:

```
action: Tick
action: Tick
action: Tick
action: BootCheck
action: TamperWallClock; wallClock' = 9
action: BootCheck
action: NTPSync
action: Tick
action: NTPSync
```

**Variant `guard`** — spec `TimeIntegrity.tla`, config `TimeIntegrity.cfg`

- ✓ `step 6: tampered = TRUE`
- ✓ `step 7: tampered = TRUE`
- ✓ `final: tampered = FALSE`

## 3. Forward-poisoned floor stays raised across a reboot ✓

A Cadence write under a spoofed-high wallClock pushes the persisted floor to 11 and raises the alert (step 6). The poisoned floor survives the reboot (prevSample resets), and because the floor is still ahead of real time, the post-reboot NTP cannot clear it.

Scenario:

```
action: Tick
action: Tick
action: Tick
action: BootCheck
action: TamperWallClock; wallClock' = 11
action: Cadence
action: Reboot; wallClock' = 11
action: NTPSync
```

**Variant `guard`** — spec `TimeIntegrity.tla`, config `TimeIntegrity.cfg`

- ✓ `step 6: tampered = TRUE`
- ✓ `step 6: floor = 11`
- ✓ `final: tampered = TRUE`

## 4. Tolerance decides whether a moderate jump is an attack ✓

Same |7-3|=4 forward jump against floor=3. With Tol=2 it exceeds tolerance and raises; with Tol=5 it is within tolerance and stays quiet. Same spec, one constant flipped.

Scenario:

```
action: Tick
action: Tick
action: Tick
action: BootCheck
action: TamperWallClock; wallClock' = 7
action: BootCheck
```

**Variant `guard`** — spec `TimeIntegrity.tla`, config `TimeIntegrity.cfg`

- ✓ `final: tampered = TRUE`

**Variant `tol_loose`** — spec `TimeIntegrity.tla`, config `TimeIntegrity.cfg`, constants Tol=5

- ✓ `final: tampered = FALSE`

