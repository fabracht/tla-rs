# Supported TLA+ Subset

tla-rs implements the Naturals, Integers, Sequences, FiniteSets, TLC, Bags, and Bits standard modules. See [`SYNTAX_STATUS.md`](SYNTAX_STATUS.md) for the full operator-by-operator coverage table.

The supported operator categories: logic (`/\`, `\/`, `~`, `=>`), comparison, arithmetic, sets (`\in`, `\union`, `\intersect`, `SUBSET`, `UNION`), functions (`[x \in S |-> e]`, `DOMAIN`, `EXCEPT`, `@@`), quantifiers (`\E`, `\A`, `CHOOSE`), records, tuples/sequences, `IF-THEN-ELSE`, `CASE`, `LET-IN`, primed variables, `UNCHANGED`, transitive closure, module instances (`INSTANCE` with qualified calls), and Unicode equivalents for all operators.

## Module Instances

Specs can use `INSTANCE` to import and compose modules:

```tla
---- MODULE pingpong ----
LOCAL INSTANCE Naturals

VARIABLES server_to_client, client_to_server

Data == [message: {"ping"}] \cup [message: {"pong"}]

ServerToClientChannel(Id) == INSTANCE MChannel WITH channels <- server_to_client
ClientToServerChannel(Id) == INSTANCE MChannel WITH channels <- client_to_server

Next ==
    \/ \E id \in ClientIds: ServerToClientChannel(id)!Send([message |-> "ping"])
    \/ \E id \in ClientIds: ClientToServerChannel(id)!Recv([message |-> "pong"])
====
```

Both static (`Alias == INSTANCE M WITH ...`) and parameterized (`Alias(p) == INSTANCE M WITH ...`) instances are supported. Library modules without Init/Next work as expected. The module file must be in the same directory as the spec.

## Spec Structure

```tla
---- MODULE Example ----
EXTENDS Naturals

CONSTANT N
VARIABLES x, y

Init == x = 0 /\ y = 0

Next ==
    \/ (x < N /\ x' = x + 1 /\ y' = y)
    \/ (y < N /\ x' = x /\ y' = y + 1)

TypeOK == x \in 0..N /\ y \in 0..N
Inv == x + y <= 2 * N
====
```

Invariants are detected by naming convention: definitions starting with `Inv`, `TypeOK`, or `NotSolved` are automatically checked.

## Limitations

`Nat` and `Int` are bounded (-100 to 100 by default). Temporal operators `[]`, `<>`, `~>` are parsed but cannot be evaluated directly — use `--check-liveness` for fairness/liveness properties via SCC analysis. Unbounded quantifiers (`\E x : P` without `\in S`) and `Seq(S)` enumeration are not supported. Recursive operators must be declared with `RECURSIVE`.
