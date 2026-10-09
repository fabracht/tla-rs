# Supported TLA+ Subset

tla-rs implements the Naturals, Integers, Sequences, FiniteSets, TLC and Bags standard modules, and a Bits module. See [`SYNTAX_STATUS.md`](SYNTAX_STATUS.md) for the full operator-by-operator coverage table.

The supported operator categories: logic (`/\`, `\/`, `~`, `=>`), comparison, arithmetic, sets (`\in`, `\union`, `\intersect`, `SUBSET`, `UNION`), functions (`[x \in S |-> e]`, `DOMAIN`, `EXCEPT`, `@@`), quantifiers (`\E`, `\A`, `CHOOSE`), records, tuples/sequences, `IF-THEN-ELSE`, `CASE`, `LET-IN`, primed variables, `UNCHANGED`, transitive closure, module instances (`INSTANCE` with qualified calls), and Unicode equivalents for the logical, comparison, set, quantifier, function and temporal operators (`⟨ ⟩`, `÷` and `≜` are not supported). Where tla-rs and TLC disagree on the same input, see [Known Differences from TLC](SYNTAX_STATUS.md#known-differences-from-tlc).

## Module Instances

Specs can use `INSTANCE` to import and compose modules. An excerpt of [`test_cases/should_pass/pingpong.tla`](test_cases/should_pass/pingpong.tla), which instantiates [`MChannel.tla`](test_cases/should_pass/MChannel.tla) once per direction:

```tla
CONSTANT NumberOfClients, NumberOfPings

VARIABLES server_to_client, client_to_server, num_pings_sent, num_pongs_received

ClientIds == 1..NumberOfClients

Data == [message: {"ping"}] \cup [message: {"pong"}]

ServerToClientChannel(Id) == INSTANCE MChannel WITH channels <- server_to_client
ClientToServerChannel(Id) == INSTANCE MChannel WITH channels <- client_to_server

ServerSendPing ==
   /\ num_pings_sent < NumberOfPings
   /\ \E client_id \in ClientIds:
      ServerToClientChannel(client_id)!Send([message |-> "ping"])
   /\ num_pings_sent' = num_pings_sent + 1
   /\ UNCHANGED<<client_to_server, num_pongs_received>>

Init ==
   /\ server_to_client = [client_id \in ClientIds |-> ServerToClientChannel(client_id)!InitValue]
   /\ client_to_server = [client_id \in ClientIds |-> ClientToServerChannel(client_id)!InitValue]
   /\ num_pings_sent = 0
   /\ num_pongs_received = 0
```

`tla test_cases/should_pass/pingpong.tla -c NumberOfClients=2 -c NumberOfPings=2 --allow-deadlock` explores 17 states.

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

Without a cfg `INVARIANT`, invariants are detected by naming convention: definitions starting with `Inv`, `TypeOK`, or `NotSolved`, and `Inv` or `TypeOK` after a module prefix that is all capitals or ends in `_` (`TPTypeOK`, `M_Inv`), are checked. A cfg `INVARIANT` (`Spec.cfg` next to `Spec.tla` is loaded automatically, or `--config PATH`) replaces detection: only the definitions it names are checked.

The standard type-invariant idiom `vars \subseteq [f1: T1, f2: T2, ...]` (and the pointwise `r \in [f1: T1, ...]`) is checked structurally — the record-type set is never enumerated, so field types may be infinite, e.g. `queue: Seq(MsgId)`. Membership verifies that the value is a record with exactly those fields and that each field value belongs to its type set (recursively, so `SUBSET S`, `[D -> R]`, and `Seq(T)` field types all work).

## Limitations

By default `Nat` is bounded to `0..100` and `Int` to `-100..100`, so `1000 \in Nat` is FALSE with no warning and `IsFiniteSet(Nat)` is TRUE. With `--symbolic-integers` (CLI, the `SYMBOLIC_INTEGERS TRUE` cfg directive, or the MCP `check_spec` `symbolic_integers` field) they become infinite symbolic sets matching TLC: membership (`x \in Nat`) and set-op membership (`x \in (Nat \ {0})`) work, `IsFiniteSet(Nat)` is `FALSE`, and any attempt to enumerate them (unbounded `\A`/`\E`, `{x \in Nat : P}`, `Cardinality`, `CHOOSE x \in Nat`, `[Nat -> T]`, `SUBSET Nat`) errors loudly. Temporal operators `[]`, `<>`, `~>` are parsed but cannot be evaluated directly — a cfg `PROPERTY` (or `--check-liveness`) checks any temporal property over state predicates and `[][A]_v` / `<<A>>_v` steps by TLC's tableau method, `ENABLED` and `WF`/`SF` inside a `PROPERTY` included (`--liveness-engine legacy` selects the engine before 0.16, which checks only a few property shapes). Unbounded quantifiers (`\E x : P` without `\in S`) and `Seq(S)` enumeration are not supported. Recursive operators must be declared with `RECURSIVE`. A function definition `f[x \in S] == e` parses only inside a `LET`, and user-defined infix operators (`a ** b == ...`) do not parse. The cfg directives `ACTION_CONSTRAINT`, `ALIAS` and `POSTCONDITION` are ignored with a warning. The full list is in [Known Differences from TLC](SYNTAX_STATUS.md#known-differences-from-tlc).
