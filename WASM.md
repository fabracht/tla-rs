# WebAssembly

The core library compiles to WASM for browser embedding. Every [GitHub release](https://github.com/fabracht/tla-rs/releases/latest) ships the built engine as `tla_checker.js` and `tla_checker_bg.wasm`. To build it from a working copy (needs [cargo-make](https://github.com/sagiegurari/cargo-make) and the `wasm32-unknown-unknown` target; a `wasm-bindgen-cli` matching `Cargo.lock` is installed into `.wasm-tools/` when missing):

```bash
cargo make wasm
```

This produces a `pkg/` directory with `tla_checker_bg.wasm`, the `tla_checker.js` bindings, and TypeScript declarations. The bindings are generated with `wasm-bindgen --target web`, so the module must be initialized before any binding is called: `await init()` (the default export, which fetches `tla_checker_bg.wasm` next to the JS file) or `initSync({ module: bytes })` with the wasm bytes.

```js
import init, { check_spec_with_options } from "./tla_checker.js";
await init();
```

The WASM API provides four checking bindings, each taking the spec source and returning a JSON string:

| Binding | Arguments |
|---------|-----------|
| `check_spec(spec, constants_json)` | Default limits (1,000,000 states, depth 100). |
| `check_spec_with_config(spec, constants_json, max_states, max_depth, allow_deadlock, export_dot)` | Explicit limits. |
| `check_spec_with_cfg(spec, cfg_source, constants_json, max_states, max_depth, allow_deadlock, export_dot)` | A TLC-style cfg plus explicit limits. |
| `check_spec_with_options(spec, options_json)` | A JSON options object (below). |

The result has `success`, `error_type` and `error_message` (`null` on success), `states_explored`, `trace` (the counterexample as an array of strings, one formatted state each, or `null`), `dot` (the DOT graph when requested, or `null`), and `warnings`.

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
| `constants` | object | Constant values (`{"N": 3, "Procs": ["a","b"]}`); a JSON array becomes a set, an object a record |
| `cfg_source` | string | TLC-style cfg file contents |
| `max_states` | number | Maximum states to explore |
| `max_depth` | number | Maximum trace depth |
| `allow_deadlock` | bool | Allow states with no successors |
| `export_dot` | bool | Include DOT graph in result |
| `dot_mode` | string | DOT export mode: `full`, `trace`, `clean` (default), `choices` |

## Stepping API

For step-by-step exploration there are four additional bindings. `explore_init`, `explore_next`, and `explore_invariants` power the [`--explorable` HTML export](CLI_GUIDE.md#demo-walkthroughs); `explore_eval` is available for embedders that want to evaluate an arbitrary expression at a state:

| Binding | Returns |
|---------|---------|
| `explore_init(spec, cfg, constants)` | The initial states. |
| `explore_next(spec, cfg, constants, state)` | The enabled transitions from a state, with action names and change deltas. |
| `explore_eval(spec, cfg, constants, state, expr)` | The value of a TLA+ expression evaluated at a state. |
| `explore_invariants(spec, cfg, constants, state)` | Each invariant's name and whether it holds at the state. |

Each takes the spec source, a cfg source string (empty for none), and a JSON constants object; the per-state bindings also take a JSON state. All return a JSON string carrying an `ok` flag (and an `error` message when `ok` is false). States round-trip through the typed JSON form produced by `explore_init`/`explore_next`, so the result of one call can be fed straight into the next.
