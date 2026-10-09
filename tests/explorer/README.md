# Explorer end-to-end test

Headless smoke test for the JavaScript that ships inside an exported
explorable demo (`--present … --export-html … --explorable`). It drives the
real embedded wasm engine in Chromium and asserts the runtime behavior that
the Rust render tests can only check as string scaffolding:

- one action row per enabled-action group
- a solo action's number-key hotkey fires the transition and advances the state
- `Backspace` steps back to the previous state
- a multi-variant group's hotkey expands its variant sublist

## Run locally

The test reads a pre-generated fixture from `fixtures/explore.html`, which
requires a `tla` binary built with the `embed-wasm` feature (so the wasm engine
is embedded in the HTML). The build below uses
[cargo-make](https://github.com/sagiegurari/cargo-make)
(`cargo install cargo-make`): `cargo make wasm` runs `wasm-bindgen` at the exact
version of the `wasm-bindgen` crate in `Cargo.lock`, installing a project-local
copy if needed, as CI does. Without cargo-make, run the two commands it wraps,
with a `wasm-bindgen-cli` of that same version:
`cargo rustc --lib --release --target wasm32-unknown-unknown --features wasm --crate-type cdylib`,
then `wasm-bindgen --target web --out-dir pkg target/wasm32-unknown-unknown/release/tla_checker.wasm`.

```bash
# from the repo root — build the wasm engine into pkg/ then a tla with it embedded
cargo make wasm
cargo build --release --bin tla --features embed-wasm

# export the fixture the test expects
mkdir -p tests/explorer/fixtures
./target/release/tla --present test_cases/demo/ExploreDemo.demo.json \
  --export-html tests/explorer/fixtures/explore.html --explorable

# run the test
cd tests/explorer
npm ci
npx playwright install chromium
npm test
```

`fixtures/` and `node_modules/` are gitignored. CI regenerates the fixture on
every run, so the test always exercises the current template.
