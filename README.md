# tla-rs

A TLA+ model checker and interactive exploration tool written in Rust.

tla-rs verifies TLA+ specifications by exploring all reachable states, checking invariants, and reporting counterexamples. Beyond pass/fail checking it offers an interactive TUI for stepping through state spaces, scenario-driven exploration, property-satisfaction analytics, parameter sweeps, tested demo walkthroughs (with an optional in-browser explorer), and an MCP server for agentic clients. The core library compiles to WebAssembly for browser embedding. It's a lightweight alternative to the official TLC model checker for specs that fit its supported subset.

## Installation

From crates.io (installs both `tla` and the `tla-mcp` server):

```bash
cargo install tla-checker
```

From a working copy:

```bash
cargo build --release
```

The binaries will be at `target/release/tla` and `target/release/tla-mcp`. Prebuilt binaries are also available via Homebrew (`brew install fabracht/tla/tla-mcp`), an install script, or GitHub releases — see the [MCP Server guide](MCP.md#install).

## Quick Start

```bash
tla spec.tla
tla spec.tla -c 'N=5' -c 'Procs={"p1","p2","p3"}'
tla spec.tla -c 'Proc={a,b,c}' --symmetry Proc
tla spec.tla --config model.cfg
tla spec.tla --quick    # limit to 10,000 states
tla spec.tla -i         # interactive TUI
```

Constants accept integers (`42`), booleans (`TRUE`), quoted strings (`"hello"`), sets (`{1,2,3}`), tuples (`<<1,2>>`), records (`[hp |-> 100]`), and functions (`a :> 1 @@ b :> 2`).

A bare identifier is a **model value** — an uninterpreted, pairwise-distinct atom, matching TLC. `n1` is not equal to the string `"n1"`, so `-c 'Proc={a,b,c}'` yields three model values, not three strings. Symmetry reduction requires a set of model values (`--symmetry` rejects a set of quoted strings, as TLC does).

## Options

The most common options are below. The [CLI Guide](CLI_GUIDE.md#options) lists every option, and `tla --help` prints them.

| Option | Description |
|--------|-------------|
| `-c`, `--constant NAME=VALUE` | Set a constant value |
| `-s`, `--symmetry CONST` | Enable symmetry reduction for a set constant |
| `--config PATH` | Load TLC-style cfg file (auto-discovers `Spec.cfg` next to `Spec.tla`) |
| `--max-states N` | Maximum states to explore (default: 1000000) |
| `--max-depth N` | Maximum trace depth (default: 100) |
| `-q`, `--quick` | Quick exploration (limit: 10,000 states) |
| `--export-dot FILE` | Export state graph to DOT format |
| `--dot-mode MODE` | DOT mode: `full`, `trace`, `clean` (default), `choices` |
| `--allow-deadlock` | Allow states with no successors |
| `--check-liveness` | Check liveness and fairness properties |
| `--liveness-engine E` | `tableau` (default: checks any temporal property as TLC does) or `legacy` (see the [CLI Guide](CLI_GUIDE.md#liveness)) |
| `--continue` | Continue past invariant violations |
| `--count-satisfying NAME` | Count states satisfying a definition (repeatable) |
| `--sweep NAME=V1;V2;...` | Sweep a constant across values, compare results |
| `--scenario TEXT` | Explore a specific scenario (or `@file`) |
| `-i`, `--interactive` | Interactive TUI exploration mode |
| `--present FILE` | Run a demo manifest (`.json`/`.toml`); TUI walkthrough, or `--validate` for a pass/fail report |
| `--export-md FILE` | With `--present`: write a Markdown walkthrough |
| `--export-html FILE` | With `--present`: write a self-contained HTML walkthrough |
| `--explorable` | With `--export-html`: embed the wasm engine for in-browser state exploration |
| `--validate` | Parse and validate the spec without model checking |
| `--json` | JSON output |
| `-v`, `--verbose` | Verbose output (depth breakdowns, etc.) |
| `-V`, `--version` | Show version information |

## Documentation

| Guide | Contents |
|-------|----------|
| [CLI Guide](CLI_GUIDE.md) | Full options reference, configuration files, scenarios, demo walkthroughs (incl. the `--explorable` browser explorer), interactive mode, analytics, output, and state-graph visualization |
| [TLA+ Support](TLA_SUPPORT.md) | Supported operator subset, module instances, spec structure, and limitations |
| [WebAssembly](WASM.md) | Browser-embeddable WASM API, including the live stepping bindings |
| [MCP Server](MCP.md) | `tla-mcp` install, client registration, and tool reference |
| [Syntax Status](SYNTAX_STATUS.md) | Operator-by-operator coverage table |
| [Architecture](ARCHITECTURE.md) | Internal design |
| [Practical TLA+ Guide](USER_GUIDE_TO_PRACTICAL_TLA.md) | Worked guidance for writing checkable specs |

## License

Licensed under either of [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your option.
