use std::fmt::Write;
use std::path::Path;

use super::beat::run_beat;
use super::manifest::Manifest;

pub fn render_doc(manifest_dir: &Path, manifest: &Manifest) -> (String, bool) {
    let mut out = String::new();
    let title = manifest
        .title
        .clone()
        .unwrap_or_else(|| "TLA+ demo".to_string());
    let _ = writeln!(out, "# {}\n", title);

    let mut all_passed = true;
    for (idx, beat) in manifest.beats.iter().enumerate() {
        let report = run_beat(manifest_dir, manifest, beat);
        let passed = report.passed();
        all_passed &= passed;
        let mark = if passed { "✓" } else { "✗" };

        let _ = writeln!(out, "## {}. {} {}\n", idx + 1, report.title, mark);
        if let Some(note) = &report.note {
            let _ = writeln!(out, "{}\n", note);
        }

        if !beat.scenario.is_empty() {
            let _ = writeln!(out, "Scenario:\n");
            let _ = writeln!(out, "```");
            for line in &beat.scenario {
                let _ = writeln!(out, "{}", line);
            }
            let _ = writeln!(out, "```\n");
        } else if let Some(replay) = &beat.replay {
            let _ = writeln!(out, "Replay: `{}`\n", replay);
        }

        for run in &report.runs {
            let _ = write!(out, "**Variant `{}`**", run.variant);
            if let Some(v) = manifest.variants.get(&run.variant) {
                let _ = write!(out, " — spec `{}`", v.spec);
                if let Some(cfg) = &v.config {
                    let _ = write!(out, ", config `{}`", cfg);
                }
                if !v.constants.is_empty() {
                    let consts: Vec<String> = v
                        .constants
                        .iter()
                        .map(|(k, val)| format!("{}={}", k, val))
                        .collect();
                    let _ = write!(out, ", constants {}", consts.join(", "));
                }
            }
            let _ = writeln!(out, "\n");

            if let Some(failure) = &run.failure {
                let _ = writeln!(out, "- **error:** {}", failure);
            }
            for assertion in &run.assertions {
                let m = if assertion.passed { "✓" } else { "✗" };
                match &assertion.detail {
                    Some(d) if !assertion.passed => {
                        let _ = writeln!(out, "- {} `{}` — {}", m, assertion.raw, d);
                    }
                    _ => {
                        let _ = writeln!(out, "- {} `{}`", m, assertion.raw);
                    }
                }
            }
            let _ = writeln!(out);
        }
    }

    (out, all_passed)
}
