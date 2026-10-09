# MCP Server

`tla-mcp` exposes the model checker as a Model Context Protocol server over stdio, so agentic clients (Claude Code, Cursor, etc.) can call it as a first-class tool.

## Install

Several paths are supported — pick whichever fits your toolchain.

**Homebrew (macOS, Linuxbrew)** — installs both `tla` and `tla-mcp`:

```bash
brew install fabracht/tla/tla-mcp
```

The formula lives in the [`fabracht/homebrew-tla`](https://github.com/fabracht/homebrew-tla) tap, which the release workflow updates on every tagged release. [`packaging/homebrew/README.md`](packaging/homebrew/README.md) describes that automation and the manual fallback.

**Install script (Linux, macOS)** — downloads a prebuilt binary and verifies its SHA256, no Rust toolchain required:

```bash
curl -fsSL https://raw.githubusercontent.com/fabracht/tla-rs/main/scripts/install.sh | bash
```

Flags go after `bash -s --`:

```bash
curl -fsSL https://raw.githubusercontent.com/fabracht/tla-rs/main/scripts/install.sh | bash -s -- --bin tla-mcp
```

`--bin tla-mcp` installs just the MCP server (`tla`, `tla-mcp` or `both`, default `both`), `--version v0.4.3` pins a release (releases prior to v0.4.3 do not ship a `SHA256SUMS` asset and are rejected), `--dir /usr/local/bin` installs system-wide (requires `sudo`; default `$HOME/.local/bin`).

**Cargo (any platform with a Rust toolchain)**:

```bash
cargo install tla-checker --bin tla-mcp
```

**GitHub release downloads** — prebuilt binaries for Linux x86_64, macOS x86_64, macOS arm64, and Windows x86_64 are attached to every [release](https://github.com/fabracht/tla-rs/releases/latest) as `tla-<platform>` and `tla-mcp-<platform>`, where `<platform>` is `linux-amd64`, `macos-amd64`, `macos-arm64` or `windows-amd64` (Windows assets end in `.exe`). Each release also carries `SHA256SUMS` and the browser engine (`tla_checker.js`, `tla_checker_bg.wasm`; see [WASM.md](WASM.md)).

**From a working copy**:

```bash
cargo install --path . --bin tla-mcp
```

## Register with your client

**Claude Code** — once `tla-mcp` is on PATH:

```bash
claude mcp add --scope user tla -- tla-mcp
```

Inside a clone of this repository no registration is needed: the checked-in [`.mcp.json`](.mcp.json) registers `tla-mcp` at project scope.

**Other MCP clients** — add to `claude_desktop_config.json` or your client's equivalent:

```json
{
  "mcpServers": {
    "tla": {
      "command": "tla-mcp"
    }
  }
}
```

To check which build is registered, run `tla-mcp --version` (or `-V`) — it prints the version and exits instead of starting the server. Note this is a different flag from the install script's `--version` above, which pins the release to download.

## Tools

All tools return a `schema_version: "2"` field — the contract is bumped explicitly on breaking changes (version 2 added the `property_violation` outcome and `properties_checked`).

| Tool | Purpose |
|------|---------|
| `validate_spec` | Parse a `.tla` file and return a summary (vars, **constants with resolved values**, invariants, init/next presence). Returns a structured parse/config error with source span on failure. Inspect the `constants` array before every `check_spec` call — outlier values are the most common cause of timeouts. |
| `list_invariants` | Return the invariants `check_spec` will verify. With a cfg `INVARIANT` directive, exactly the definitions it lists; without one, the zero-argument definitions detected by name: `Inv*`, `TypeOK*`, `NotSolved*`, or a module prefix followed by `Inv`/`TypeOK` (`MInv`, `M_TypeOK`). |
| `check_spec` | Run full model checking. **Requires** `max_states`, `max_depth`, AND `max_seconds` (no defaults — agents must budget all three upfront). The `max_seconds` budget is enforced during both BFS exploration and the liveness phase. Returns one of: `ok`, `invariant_violation` (with trace + invariant name + actions), `deadlock`, `liveness_violation` (with prefix + cycle), `property_violation` (a cfg `PROPERTY` failing on an initial state, `kind: "init"`, or on a transition, `kind: "action"`; with property name + trace + actions), `limit_reached` (budget exhausted — not an error; `limit` is one of `max_states`/`max_depth`/`max_seconds`), or `error` (with structured phase + message + optional source span; phase `liveness` is an evaluation error while checking a liveness property after the state search, with the property named in the message and `partial_stats` set). |
| `replay_scenario` | Walk a spec step-by-step through a guided scenario. Each line is `step: <TLA+ expression>` (the transition satisfying the expression; primed variables refer to the next state) or `action: <Name>` (the transition produced by that action, optionally constrained further as `action: <Name>; <expression>`). Returns the same `StateSnapshot` shape as `check_spec`, plus per-step `changes` descriptions. On a step that no transition satisfies, returns `status: "failed"` with `available_actions` to help diagnose the mismatch. |
| `validate_demo` | Run a demo manifest (named variants + ordered beats) and report pass/fail per beat and variant, with the failing assertions on a miss. |
| `append_beat` | Append a beat to a manifest, persisting it only if all its assertions pass. Format-preserving — a `.toml` manifest stays TOML. |
| `export_demo_doc` | Render a demo manifest to a tested Markdown walkthrough at `out_path`. |
| `export_demo_html` | Render a demo manifest to a self-contained, offline HTML walkthrough. Pass `explorable: true` to embed the wasm engine as a live in-browser state explorer (step actions via number-key hotkeys, actions grouped by name, combinatorial variants collapsed into per-variable value pickers, live invariants) — requires a `tla-mcp` built with the `embed-wasm` feature, which the prebuilt release binaries are. |

On `ok`, `properties_checked` lists the cfg `PROPERTY` names that were checked. A `[]P` conjunct of a `PROPERTY` fails as an `invariant_violation` naming the property.

`check_spec`, `validate_spec`, `list_invariants` and `replay_scenario` accept `liveness_engine: "tableau" | "legacy"` (default `tableau`, same as the CLI `--liveness-engine`). `tableau` checks any temporal `PROPERTY` by TLC's tableau method and classifies `PROPERTY` conjuncts on their syntax as TLC does; it also checks `ENABLED` and `WF`/`SF` inside a property (a `WF`/`SF` there is an obligation, so a property can be a whole abstract specification), and a property that uses `TLCGet`, `RandomElement` or the time built-ins is reported before the state search as an `error` with `phase: "config"`. `legacy` selects the engine before 0.16, which checks only a few property shapes. The other three tools take the option so their summaries reflect the same classification `check_spec` will use, and `validate_spec` with `tableau` also reports a property the engine cannot check.

The boolean toggles `allow_deadlock` and `check_liveness` are `Option<bool>` — omit them to defer to the cfg file (e.g., `CHECK_DEADLOCK FALSE` or `PROPERTY` directives), pass `true` / `false` to override the cfg. The `symmetry` field appends to any constants declared via cfg `SYMMETRY` rather than replacing them.

`validate_spec`, `list_invariants` and `check_spec` include a `warnings` array surfacing parser-tolerance warnings — when the parser fails to parse an operator body it silently skips that operator and emits a warning. The same array also surfaces temporal constructs that the legacy extraction from a `*Spec` definition drops (`<<A>>_v` diamond actions, `\E x \in S : P` with `P` other than `<>Q` or `[]<>Q`), cfg warnings, and, on `check_spec`, boolean definitions that look like invariants but are not checked and the deprecation notice for a `*Spec` definition's temporal conjuncts checked as properties without a cfg `SPECIFICATION`. Without the warnings array, a typo in an invariant's body would let `check_spec` "pass" without ever checking that invariant.

`check_spec` honors the cfg's `CONSTRAINT` directive (state-space pruning predicate) and accepts an inline `state_constraint: "<TLA+ expression>"` parameter. Constraints are evaluated on every state. A state where the expression is false is still checked against the invariants, as in TLC, but its successors are not explored. Use this to bound otherwise-explosive state spaces (e.g., `state_constraint: "Len(queue) <= 3"`) without modifying the spec.

### Common inputs

`check_spec`, `validate_spec`, `list_invariants` and `replay_scenario` take:

| Input | Description |
|-------|-------------|
| `spec_path` | Path to the `.tla` file (required). |
| `config_path` | Path to a cfg file. When omitted, `<spec>.cfg` next to the spec is loaded if it exists. |
| `constants` | Map of constant name to value string, in the same formats as the CLI `--constant` (`"3"`, `"{p1, p2}"`, `"<<1, 2>>"`). Overrides a cfg constant of the same name. |
| `liveness_engine` | `"tableau"` (default) or `"legacy"` (above). |

`check_spec` additionally takes:

| Input | Description |
|-------|-------------|
| `max_states`, `max_depth`, `max_seconds` | Budgets (required, no defaults). |
| `allow_deadlock`, `check_liveness` | Optional booleans; omit to defer to the cfg. |
| `symmetry` | Name of a set constant of model values to reduce by symmetry. |
| `symbolic_integers` | Optional boolean, as cfg `SYMBOLIC_INTEGERS`: `Nat`/`Int` become infinite sets decided by membership instead of `0..100` / `-100..100`. |
| `state_constraint` | Inline constraint expression (above). |
| `count_satisfying` | Names of zero-argument boolean definitions to evaluate on every reachable state; counts come back in `stats.property_stats` as `{name, satisfied, violated, errors}`. |
| `continue_on_violation` | Default `false`. When `true`, invariant violations (and violations of a `PROPERTY`'s `[][A]_v` parts) are counted instead of ending the run: the result reports the outcome of the rest of the search (`ok` if nothing else fails, unlike the CLI's `--continue --json`: [#196](https://github.com/fabracht/tla-rs/issues/196)) and lists the counts in `stats.violations` (`{kind, name, count}`) and `stats.violation_count`, without traces. |

### Outputs

`check_spec` returns `stats` with `states_explored`, `transitions`, `max_depth_reached`, `elapsed_secs` and `actions` (per-action transition counts, `{name, transitions}`), plus `property_stats`, `violations` and `violation_count` when the options above produce them. An `error` outcome carries `partial_stats` when the state search had run, as for phase `liveness`. The top-level `advisories` array flags budgets that are usually a mistake (`max_depth` over 100, `max_states` over 1,000,000) before the run. `validate_spec` returns `spec` with `vars`, `constants` (each with its resolved value), `invariants`, `has_init`, `has_next` and `definition_count`.

## Counterexample format

Each state in a trace is `{ vars: { var_name: { display, json } } }`. The `display` field is the TLA+-formatted value (`"{1, 2, 3}"`, `"<<a, b>>"`); the `json` field is a typed JSON form preserving set/tuple/record/function structure via a `kind` tag (`{"kind": "set", "elements": [0, 1]}`); integers, booleans and strings are plain JSON values.

## Mid-session reload

MCP clients spawn server processes at session startup. Rebuilding or reinstalling `tla-mcp` while a Claude Code session is already running will not hot-reload the new binary — restart the client (or open a new session) to pick up changes. Verifying outside an MCP client: `tla-mcp` invoked directly will exit with `ConnectionClosed` after stdin EOF, which is the correct behavior for a stdio server with no peer.

## Observability

See [`docs/MCP_OBSERVABILITY.md`](docs/MCP_OBSERVABILITY.md) for per-action stats, advisories, and the doc tracker.
