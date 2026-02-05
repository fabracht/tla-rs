# Examples

## c3po_asteroid_field.tla

The Millennium Falcon navigating the Empire Strikes Back asteroid field. Models asteroid impacts, TIE fighter attacks, TIEs destroyed by asteroids, hiding in the space slug's cave, mynock damage, escaping the exogorth, and the only real escape — attaching to a Star Destroyer's hull. Shields, hull integrity, and ship systems (sensors, engines, weapons) all degrade under damage.

```bash
tla examples/c3po_asteroid_field.tla -c 'Density=3' --allow-deadlock --continue \
  --count-satisfying InvNeverTellMeTheOdds --count-satisfying Escaped --verbose
```

## counter.tla

A counter that increments from 0 to 5. Good starting point for understanding how specs, invariants, and state exploration work.

```bash
tla examples/counter.tla
```

## counter_bug.tla

Same counter, but the bound is wrong — it tries to count to 10 while the invariant enforces `count <= 5`. Demonstrates how tla-rs reports invariant violations with counterexample traces.

```bash
tla examples/counter_bug.tla
```

## traffic_light.tla

A three-state traffic light cycling through red, yellow, and green with a cycle counter. Shows how to model simple state machines.

```bash
tla examples/traffic_light.tla
```

## coffee_simple.tla

Picking black beans from a coffee can with bounded counts. A minimal example of set-like reasoning over discrete quantities.

```bash
tla examples/coffee_simple.tla --allow-deadlock
```

## coffee_record.tla

Coffee can modeled with records tracking black and white bean counts. Shows how to use records and field access in specs.

```bash
tla examples/coffee_record.tla --allow-deadlock
```

## coffee_debug.tla

Debug variant of the coffee can for stepping through transitions interactively.

```bash
tla examples/coffee_debug.tla --allow-deadlock -i
```

## mutex.tla

Two processes competing for a critical section, protected by a lock. `Acquire` checks the lock is free before entering. `InvMutualExclusion` asserts at most one process is in the critical section at any time.

```bash
tla examples/mutex.tla -c 'Procs={"p1","p2"}' --allow-deadlock
```

## mutex_bug.tla

Same mutex, but `Acquire` skips the lock check — a process enters the critical section without verifying the lock is free. The checker immediately finds two processes in the critical section simultaneously.

```bash
tla examples/mutex_bug.tla -c 'Procs={"p1","p2"}' --allow-deadlock
```
