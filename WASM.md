# WebAssembly

The core library compiles to WASM for browser embedding:

```bash
cargo make wasm
```

This produces a `pkg/` directory with the WASM module and JS bindings. The WASM API provides `check_spec`, `check_spec_with_config`, `check_spec_with_cfg`, and `check_spec_with_options` — all returning JSON results with success status, state count, error traces, and optional DOT graph output.

The `check_spec_with_options` API accepts a JSON options object:

```js
const result = JSON.parse(check_spec_with_options(specSource, JSON.stringify({
  constants: { N: 3 },
  max_states: 10000,
  max_depth: 50,
  allow_deadlock: true,
  export_dot: true,
  dot_mode: "choices",   // "full", "trace", "clean" (default), "choices"
  cfg_source: "INIT Init\nNEXT Next\n"
})));

if (result.dot) {
  // DOT graph string: "digraph StateGraph { ... }"
}
```

| Option | Type | Description |
|--------|------|-------------|
| `constants` | object | Constant values (`{"N": 3, "Procs": ["a","b"]}`) |
| `cfg_source` | string | TLC-style cfg file contents |
| `max_states` | number | Maximum states to explore |
| `max_depth` | number | Maximum trace depth |
| `allow_deadlock` | bool | Allow states with no successors |
| `export_dot` | bool | Include DOT graph in result |
| `dot_mode` | string | DOT export mode: `full`, `trace`, `clean` (default), `choices` |

## Stepping API

For step-by-step exploration there are four additional bindings, which power the [`--explorable` HTML export](CLI_GUIDE.md#demo-walkthroughs):

| Binding | Returns |
|---------|---------|
| `explore_init(spec, cfg, constants)` | The initial states. |
| `explore_next(spec, cfg, constants, state)` | The enabled transitions from a state, with action names and change deltas. |
| `explore_eval(spec, cfg, constants, state, expr)` | The value of a TLA+ expression evaluated at a state. |
| `explore_invariants(spec, cfg, constants, state)` | Each invariant's name and whether it holds at the state. |

Each takes the spec source, an optional cfg source string, and a JSON constants object; the per-state bindings also take a JSON state. All return a JSON string carrying an `ok` flag (and an `error` message when `ok` is false). States round-trip through the typed JSON form produced by `explore_init`/`explore_next`, so the result of one call can be fed straight into the next.
