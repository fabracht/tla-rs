# Interactive Mode

Interactive mode lets you manually explore a TLA+ specification's state space, step through actions, and debug invariant violations.

```bash
cargo run -- your_spec.tla -i
```

## Layout

```
┌─────────────────────────────────────────────────────────────┐
│ Objectives (Invariants) - shows pass/fail status            │
├─────────────────────────────────────────────────────────────┤
│ State - current variable values                             │
├─────────────────────────────────────────────────────────────┤
│ Actions - available transitions from current state          │
├─────────────────────────────────────────────────────────────┤
│ Trace - history of actions taken                            │
├─────────────────────────────────────────────────────────────┤
│ Status bar - keybindings and messages                       │
└─────────────────────────────────────────────────────────────┘
```

When a tool is active (trace, REPL, hypothesis), the state panel splits to show tool output on the right.

## Keybindings

### Navigation

| Key | Action |
|-----|--------|
| `↑` / `k` | Select previous action |
| `↓` / `j` | Select next action |
| `Enter` | Execute selected action |
| `b` / `Backspace` | Undo - go back one step |
| `r` | Reset to initial state |
| `q` / `Esc` | Quit |

### Tools

| Key | Tool | Description |
|-----|------|-------------|
| `t` | Variable Trace | See how variables changed over time |
| `e` | REPL | Evaluate TLA+ expressions |
| `h` | Hypothesis | Test if a guard would block past transitions |
| `g` | Guards | Toggle guard visibility on actions |

### File Operations

| Key | Action |
|-----|--------|
| `s` | Save current trace to `trace.json` |
| `l` | Load trace from `trace.json` |

---

## Variable Trace (`t`)

Shows how variables changed throughout your exploration.

1. Execute some actions with `Enter`
2. Press `t` to open trace panel
3. Type to filter (e.g., `count` or `msgs`) - filters live as you type
4. Press `Enter` or `Esc` to close

Example output:
```
> small█

 ├ [1] small = 0 → 3  FillSmallJug
 ├ [2] small = 3 → 0  EmptySmallJug
 └ [4] small = 0 → 2  BigToSmall
```

The numbers `[1]`, `[2]`, etc. are state indices showing when each change occurred.

---

## REPL (`e`)

Evaluate any TLA+ expression using the current state's variables.

1. Press `e` to open REPL
2. Type an expression and press `Enter`
3. Press `Esc` to close

Examples:
```
> big + small
= 5

> big = 4
= FALSE

> count \in 0..10
= TRUE

> {x \in 1..10 : x > 5}
= {6, 7, 8, 9, 10}
```

---

## Hypothesis Testing (`h`)

Test whether adding a guard would have blocked past transitions. Useful for debugging: "Would this fix have prevented the bug?"

1. Execute actions to build up history
2. Press `h` to open hypothesis panel
3. Enter a guard expression (a boolean condition)
4. See which past transitions would have been blocked

Example:
```
> count > 0█

Testing guard: count > 0

State 0→1: Increment
  Guard: 0 > 0 = FALSE
  ✗ Would be BLOCKED

State 1→2: Increment
  Guard: 1 > 0 = TRUE
  ✓ Would pass

1 of 3 transitions would be blocked
```

---

## Guard Visibility (`g`)

Shows the preconditions (guards) for each available action. Guards are conditions that must be true for an action to be enabled.

Press `g` to toggle. When enabled:
```
 ▸ [1] Increment: count': 0 -> 1
       ✓ count < 5
   [2] Decrement: (no changes)
       ✗ count > 0
   [3] Reset: (no changes)
       ✗ count >= 3
```

- `✓` (green) = condition is true, action is enabled
- `✗` (red) = condition is false, action would be blocked
- `(no preconditions)` = action has no guards, always enabled

This helps answer "Why is this action available?" or "Why can't I do X?"

---

## Counterexample Replay

When model checking finds an invariant violation, you can save and replay it.

### Save counterexample during check:
```bash
cargo run -- spec.tla --save-counterexample violation.json
```

### Replay interactively:
```bash
cargo run -- spec.tla --replay violation.json
```

In replay mode:
- `n` / `→` - Next state in trace
- `p` / `←` - Previous state
- `e` - Open REPL to inspect current state
- `q` - Quit

---

## Tips

1. **Start with a simple exploration**: Execute a few actions, then use `t` to see what changed.

2. **Use REPL to check conditions**: Before taking an action, use `e` to evaluate expressions like `count < 5` to understand the state.

3. **Guards explain "why"**: If you're confused why an action is available (or not), press `g` to see its preconditions.

4. **Hypothesis for debugging**: Found a bug? Use `h` to test if a proposed fix (new guard) would have prevented it.

5. **Save interesting traces**: Press `s` to save your exploration. Load it later with `l` to continue.
