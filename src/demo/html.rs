use std::path::Path;

use serde_json::{Map, Value as J, json};

use crate::checker::format_value;

use super::beat::run_beat;
use super::manifest::Manifest;

const TEMPLATE: &str = include_str!("walkthrough.html");

pub fn render_html(manifest_dir: &Path, manifest: &Manifest) -> (String, bool) {
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
                        json!({
                            "label": step.label,
                            "changes": step.changes,
                            "vars": J::Object(vars),
                        })
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

    let data = json!({
        "title": manifest.title.clone().unwrap_or_else(|| "TLA+ demo".to_string()),
        "beats": beats,
    });

    let data_str = serde_json::to_string(&data)
        .unwrap_or_else(|_| "{}".to_string())
        .replace("</", "<\\/");

    (TEMPLATE.replace("/*DEMO_DATA*/", &data_str), all_passed)
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
}
