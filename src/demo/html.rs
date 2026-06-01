use std::path::Path;

use serde_json::{Map, Value as J, json};

use crate::checker::format_value;

use super::beat::run_beat;
use super::manifest::Manifest;

const TEMPLATE: &str = include_str!("templates/walkthrough.html");

pub fn render_html(manifest_dir: &Path, manifest: &Manifest) -> (String, bool) {
    let (beats, all_passed) = build_beats_json(manifest_dir, manifest, false);

    let data = json!({
        "title": manifest.title.clone().unwrap_or_else(|| "TLA+ demo".to_string()),
        "beats": beats,
    });

    let data_str = serde_json::to_string(&data)
        .unwrap_or_else(|_| "{}".to_string())
        .replace("</", "<\\/");

    (TEMPLATE.replace("/*DEMO_DATA*/", &data_str), all_passed)
}

fn build_beats_json(
    manifest_dir: &Path,
    manifest: &Manifest,
    include_state_json: bool,
) -> (Vec<J>, bool) {
    let mut all_passed = true;
    let mut beats: Vec<J> = Vec::new();

    for (idx, beat) in manifest.beats.iter().enumerate() {
        let report = run_beat(manifest_dir, manifest, beat);
        all_passed &= report.passed();

        let runs: Vec<J> = report
            .runs
            .iter()
            .map(|run| {
                let trace: Vec<J> = run
                    .trace
                    .iter()
                    .map(|step| {
                        let mut vars = Map::new();
                        for (i, name) in run.vars.iter().enumerate() {
                            if let Some(value) = step.state.values.get(i) {
                                vars.insert(name.to_string(), J::String(format_value(value)));
                            }
                        }
                        let mut entry = json!({
                            "label": step.label,
                            "changes": step.changes,
                            "vars": J::Object(vars),
                        });
                        if include_state_json {
                            entry["json"] = crate::trace_io::state_to_json(&step.state, &run.vars);
                        }
                        entry
                    })
                    .collect();

                let assertions: Vec<J> = run
                    .assertions
                    .iter()
                    .map(|a| {
                        json!({
                            "expectation": a.raw,
                            "passed": a.passed,
                            "detail": a.detail,
                        })
                    })
                    .collect();

                json!({
                    "variant": run.variant,
                    "passed": run.passed(),
                    "failure": run.failure,
                    "vars": run.vars.iter().map(|v| v.to_string()).collect::<Vec<_>>(),
                    "trace": trace,
                    "assertions": assertions,
                })
            })
            .collect();

        beats.push(json!({
            "index": idx,
            "title": report.title,
            "note": report.note,
            "passed": report.passed(),
            "scenario": beat.scenario,
            "runs": runs,
        }));
    }

    (beats, all_passed)
}

#[cfg(feature = "embed-wasm")]
fn variant_constant_json(raw: &str) -> J {
    match crate::config::parse_constant_value(raw) {
        Some(value) => crate::trace_io::value_to_json(&value),
        None => J::String(raw.to_string()),
    }
}

#[cfg(feature = "embed-wasm")]
fn build_variants(manifest_dir: &Path, manifest: &Manifest) -> J {
    let mut map = Map::new();
    for (name, variant) in &manifest.variants {
        let spec = std::fs::read_to_string(manifest_dir.join(&variant.spec)).unwrap_or_default();
        let cfg = match &variant.config {
            Some(c) => std::fs::read_to_string(manifest_dir.join(c)).ok(),
            None => {
                std::fs::read_to_string(manifest_dir.join(&variant.spec).with_extension("cfg")).ok()
            }
        };
        let constants: Map<String, J> = variant
            .constants
            .iter()
            .map(|(k, raw)| (k.clone(), variant_constant_json(raw)))
            .collect();
        map.insert(
            name.clone(),
            json!({ "spec": spec, "cfg": cfg, "constants": J::Object(constants) }),
        );
    }
    J::Object(map)
}

#[cfg(feature = "embed-wasm")]
const EXPLORABLE_TEMPLATE: &str = include_str!("templates/explorable.html");
#[cfg(feature = "embed-wasm")]
const WASM_BYTES: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/pkg/tla_checker_bg.wasm"
));
#[cfg(feature = "embed-wasm")]
const WASM_GLUE: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/pkg/tla_checker.js"));

#[cfg(feature = "embed-wasm")]
pub fn render_explorable(
    manifest_dir: &Path,
    manifest: &Manifest,
) -> Result<(String, bool), String> {
    use base64::Engine;

    let (beats, all_passed) = build_beats_json(manifest_dir, manifest, true);

    let data = json!({
        "title": manifest.title.clone().unwrap_or_else(|| "TLA+ demo".to_string()),
        "beats": beats,
        "variants": build_variants(manifest_dir, manifest),
    });
    let data_str = serde_json::to_string(&data)
        .unwrap_or_else(|_| "{}".to_string())
        .replace("</", "<\\/");
    let glue = WASM_GLUE.replace("</", "<\\/");
    let b64 = base64::engine::general_purpose::STANDARD.encode(WASM_BYTES);

    let html = EXPLORABLE_TEMPLATE
        .replace("/*WASM_GLUE*/", &glue)
        .replace("/*WASM_B64*/", &b64)
        .replace("/*DEMO_DATA*/", &data_str);
    Ok((html, all_passed))
}

#[cfg(not(feature = "embed-wasm"))]
pub fn render_explorable(
    _manifest_dir: &Path,
    _manifest: &Manifest,
) -> Result<(String, bool), String> {
    Err(
        "explorable HTML export requires building with --features embed-wasm \
         (run `cargo make wasm` first to produce pkg/tla_checker_bg.wasm and pkg/tla_checker.js)"
            .to_string(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn html_is_self_contained_and_embeds_beats() {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("test_cases/demo");
        let manifest = Manifest::load(&dir.join("Counter.demo.json")).unwrap();
        let (html, all_passed) = render_html(&dir, &manifest);

        assert!(all_passed);
        assert!(
            !html.contains("/*DEMO_DATA*/"),
            "placeholder must be replaced"
        );
        assert!(
            !html.contains("http://"),
            "must not reference external http"
        );
        assert!(
            !html.contains("https://"),
            "must not reference external https"
        );
        assert!(html.contains("const DATA ="));
        assert!(html.contains("Counter overflow demo"));
        assert!(html.contains("Three increments"));
    }

    #[cfg(feature = "embed-wasm")]
    #[test]
    fn explorable_html_embeds_engine_and_is_self_contained() {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("test_cases/demo");
        let manifest = Manifest::load(&dir.join("Counter.demo.json")).unwrap();
        let (html, all_passed) = render_explorable(&dir, &manifest).expect("explorable render");

        assert!(all_passed);
        assert!(!html.contains("/*WASM_GLUE*/"), "glue placeholder replaced");
        assert!(!html.contains("/*WASM_B64*/"), "wasm placeholder replaced");
        assert!(!html.contains("/*DEMO_DATA*/"), "data placeholder replaced");
        assert!(
            !html.contains("const WASM_B64 = \"\""),
            "embedded wasm must be non-empty"
        );
        assert!(
            html.contains("export function explore_init"),
            "engine bindings must be inlined"
        );
        assert!(
            !html.contains("http://"),
            "must not reference external http"
        );
        assert!(
            !html.contains("https://"),
            "must not reference external https"
        );
        assert!(
            html.contains("const HOTKEYS ="),
            "explorer must wire number-key hotkeys"
        );
        assert!(
            html.contains("arow-") && html.contains("agroup-head"),
            "explorer must render grouped, hotkeyed action rows"
        );
        assert!(
            !html.contains("ex-repl") && !html.contains("repl-out"),
            "dropped Evaluate/REPL column must not reappear"
        );
    }

    #[cfg(not(feature = "embed-wasm"))]
    #[test]
    fn explorable_render_requires_embed_wasm_feature() {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("test_cases/demo");
        let manifest = Manifest::load(&dir.join("Counter.demo.json")).unwrap();
        let err = render_explorable(&dir, &manifest).unwrap_err();
        assert!(
            err.contains("embed-wasm"),
            "error should name the required feature: {err}"
        );
    }
}
