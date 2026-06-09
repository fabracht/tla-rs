# MCP Server

`tla-mcp` exposes the model checker as a Model Context Protocol server over stdio, so agentic clients (Claude Code, Cursor, etc.) can call it as a first-class tool.

## Install

Several paths are supported — pick whichever fits your toolchain.

**Homebrew (macOS, Linuxbrew)** — installs both `tla` and `tla-mcp`:

```bash
brew install fabracht/tla/tla-mcp
```

Requires the `homebrew-tla` tap to exist. The formula source lives at [`packaging/homebrew/tla-mcp.rb`](packaging/homebrew/tla-mcp.rb); [`packaging/homebrew/README.md`](packaging/homebrew/README.md) explains the one-time tap setup.

**Install script (Linux, macOS)** — downloads a prebuilt binary and verifies its SHA256, no Rust toolchain required:

```bash
curl -fsSL https://raw.githubusercontent.com/fabracht/tla-rs/main/scripts/install.sh | bash
```

Pass flags to scope the install: `--bin tla-mcp` for just the MCP server, `--version v0.4.3` to pin a release (releases prior to v0.4.3 do not ship a `SHA256SUMS` asset and are rejected), `--dir /usr/local/bin` for a system-wide install (requires `sudo`).

**Cargo (any platform with a Rust toolchain)**:

```bash
cargo install tla-checker --bin tla-mcp
```

**GitHub release downloads** — prebuilt binaries for Linux x86_64, macOS x86_64, macOS arm64, and Windows x86_64 are attached to every [release](https://github.com/fabracht/tla-rs/releases/latest) as `tla-<platform>` and `tla-mcp-<platform>`.

**From a working copy**:

```bash
cargo install --path . --bin tla-mcp
```

## Register with your client

**Claude Code (community plugin marketplace)** — once `tla-mcp` is on PATH:

```
/plugin marketplace add anthropics/claude-plugins-community
/plugin install tla-rs@claude-community
```

**Manual registration (any MCP client)** — add to `~/.claude/mcp.json`, `claude_desktop_config.json`, or your client's equivalent:

```json
{
  "mcpServers": {
    "tla": {
      "command": "tla-mcp"
    }
  }
}
```

## Tools

All tools return a `schema_version: "1"` field — the contract is frozen at version 1 and will be bumped explicitly on breaking changes.

| Tool | Purpose |
|------|---------|
| `validate_spec` | Parse a `.tla` file and return a summary (vars, **constants with resolved values**, invariants, init/next presence). Returns a structured parse/config error with source span on failure. Inspect the `constants` array before every `check_spec` call — outlier values are the most common cause of timeouts. |
| `list_invariants` | Return the detected invariants (definitions matching `Inv*`, `TypeOK*`, `NotSolved*`, plus anything declared in a cfg `INVARIANT` directive). |
| `check_spec` | Run full model checking. **Requires** `max_states`, `max_depth`, AND `max_seconds` (no defaults — agents must budget all three upfront). The `max_seconds` budget is enforced during both BFS exploration and the liveness phase. Returns one of: `ok`, `invariant_violation` (with trace + invariant name + actions), `deadlock`, `liveness_violation` (with prefix + cycle), `limit_reached` (budget exhausted — not an error; `limit` is one of `max_states`/`max_depth`/`max_seconds`), or `error` (with structured phase + message + optional source span). |
| `replay_scenario` | Walk a spec step-by-step through a guided scenario (text of `step: <TLA+ expression>` lines). Returns the same `StateSnapshot` shape as `check_spec`, plus per-step `changes` descriptions. On a step that no transition satisfies, returns `status: "failed"` with `available_actions` to help diagnose the mismatch. |
| `validate_demo` | Run a demo manifest (named variants + ordered beats) and report pass/fail per beat and variant, with the failing assertions on a miss. |
| `append_beat` | Append a beat to a manifest, persisting it only if all its assertions pass. Format-preserving — a `.toml` manifest stays TOML. |
| `export_demo_doc` | Render a demo manifest to a tested Markdown walkthrough at `out_path`. |
| `export_demo_html` | Render a demo manifest to a self-contained, offline HTML walkthrough. Pass `explorable: true` to embed the wasm engine as a live in-browser state explorer (step actions via number-key hotkeys, actions grouped by name, combinatorial variants collapsed into per-variable value pickers, live invariants) — requires a `tla-mcp` built with the `embed-wasm` feature, which the prebuilt release binaries are. |

The boolean toggles `allow_deadlock` and `check_liveness` are `Option<bool>` — omit them to defer to the cfg file (e.g., `CHECK_DEADLOCK FALSE` or `PROPERTY` directives), pass `true` / `false` to override the cfg. The `symmetry` field appends to any constants declared via cfg `SYMMETRY` rather than replacing them.

`validate_spec` and `list_invariants` include a `warnings` array surfacing parser-tolerance warnings — when the parser fails to parse an operator body it silently skips that operator and emits a warning. The same array also surfaces unsupported temporal constructs (`<<A>>_v` diamond actions, `<>[]P` stable-eventually) that the fairness extractor drops. Without the warnings array, a typo in an invariant's body would let `check_spec` "pass" without ever checking that invariant.

`check_spec` honors the cfg's `CONSTRAINT` directive (state-space pruning predicate) and accepts an inline `state_constraint: "<TLA+ expression>"` parameter. Constraints are evaluated on every state — states where the expression is false are dropped from the reachable set and not explored further. Use this to bound otherwise-explosive state spaces (e.g., `state_constraint: "Len(queue) <= 3"`) without modifying the spec.

## Counterexample format

Each state in a trace is `{ vars: { var_name: { display, json } } }`. The `display` field is the TLA+-formatted value (`"{1, 2, 3}"`, `"<<a, b>>"`); the `json` field is a typed JSON form preserving set/tuple/record/function structure via a `kind` tag.

## Mid-session reload

MCP clients spawn server processes at session startup. Rebuilding or reinstalling `tla-mcp` while a Claude Code session is already running will not hot-reload the new binary — restart the client (or open a new session) to pick up changes. Verifying outside an MCP client: `tla-mcp` invoked directly will exit with `ConnectionClosed` after stdin EOF, which is the correct behavior for a stdio server with no peer.

## Observability

See [`docs/MCP_OBSERVABILITY.md`](docs/MCP_OBSERVABILITY.md) for per-action stats, advisories, and the doc tracker.
