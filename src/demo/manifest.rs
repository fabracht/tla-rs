use std::collections::BTreeMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

fn default_schema_version() -> String {
    "1".to_string()
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Manifest {
    #[serde(default = "default_schema_version")]
    pub schema_version: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub title: Option<String>,
    pub variants: BTreeMap<String, Variant>,
    pub beats: Vec<Beat>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Variant {
    pub spec: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub config: Option<String>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub constants: BTreeMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Beat {
    pub title: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub variant: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub compare: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub scenario: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replay: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub expect: Vec<String>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub expect_per_variant: BTreeMap<String, Vec<String>>,
}

fn is_toml_path(path: &Path) -> bool {
    path.extension()
        .and_then(|e| e.to_str())
        .is_some_and(|e| e.eq_ignore_ascii_case("toml"))
}

impl Manifest {
    pub fn load(path: &Path) -> Result<Manifest, String> {
        let contents = std::fs::read_to_string(path)
            .map_err(|e| format!("failed to read manifest {}: {}", path.display(), e))?;
        let manifest: Manifest = if is_toml_path(path) {
            toml::from_str(&contents).map_err(|e| format!("manifest TOML parse error: {}", e))?
        } else {
            serde_json::from_str(&contents)
                .map_err(|e| format!("manifest JSON parse error: {}", e))?
        };
        manifest.validate()?;
        Ok(manifest)
    }

    pub fn parse(contents: &str) -> Result<Manifest, String> {
        let manifest: Manifest = serde_json::from_str(contents)
            .map_err(|e| format!("manifest JSON parse error: {}", e))?;
        manifest.validate()?;
        Ok(manifest)
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).unwrap_or_default()
    }

    pub fn to_toml(&self) -> Result<String, String> {
        toml::to_string_pretty(self).map_err(|e| format!("manifest TOML serialize error: {}", e))
    }

    pub fn serialize_for(&self, path: &Path) -> Result<String, String> {
        if is_toml_path(path) {
            self.to_toml()
        } else {
            Ok(self.to_json())
        }
    }

    pub fn validate(&self) -> Result<(), String> {
        if self.variants.is_empty() {
            return Err("manifest has no variants".to_string());
        }
        for (i, beat) in self.beats.iter().enumerate() {
            let label = format!("beat {} ({:?})", i, beat.title);

            if !beat.compare.is_empty() && beat.variant.is_some() {
                return Err(format!("{}: set only one of `variant` or `compare`", label));
            }
            let targets = beat.target_variants();
            if targets.is_empty() {
                return Err(format!("{}: must set `variant` or `compare`", label));
            }
            for v in &targets {
                if !self.variants.contains_key(v) {
                    return Err(format!("{}: unknown variant {:?}", label, v));
                }
            }

            match (beat.scenario.is_empty(), beat.replay.is_none()) {
                (true, true) => {
                    return Err(format!("{}: must set `scenario` or `replay`", label));
                }
                (false, false) => {
                    return Err(format!("{}: set only one of `scenario` or `replay`", label));
                }
                _ => {}
            }

            for v in beat.expect_per_variant.keys() {
                if !self.variants.contains_key(v) {
                    return Err(format!(
                        "{}: expect_per_variant references unknown variant {:?}",
                        label, v
                    ));
                }
            }
        }
        Ok(())
    }
}

impl Beat {
    pub fn target_variants(&self) -> Vec<String> {
        if !self.compare.is_empty() {
            self.compare.clone()
        } else if let Some(v) = &self.variant {
            vec![v.clone()]
        } else {
            Vec::new()
        }
    }

    pub fn expectations_for(&self, variant: &str) -> &[String] {
        match self.expect_per_variant.get(variant) {
            Some(list) => list,
            None => &self.expect,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn toml_round_trip_simple() {
        let json = r#"{
            "title": "t",
            "variants": { "v": { "spec": "S.tla" } },
            "beats": [
                { "title": "b", "variant": "v", "scenario": ["action: A"],
                  "expect": ["final: x = 1"] }
            ]
        }"#;
        let manifest = Manifest::parse(json).unwrap();
        let toml_str = manifest.to_toml().unwrap();
        let back: Manifest = toml::from_str(&toml_str).unwrap();
        back.validate().unwrap();
        assert_eq!(back.beats.len(), 1);
        assert_eq!(back.beats[0].scenario, vec!["action: A".to_string()]);
        assert_eq!(back.beats[0].variant.as_deref(), Some("v"));
    }

    #[test]
    fn toml_round_trip_compare_and_per_variant() {
        let json = r#"{
            "title": "t",
            "variants": {
                "a": { "spec": "S.tla" },
                "b": { "spec": "S.tla", "constants": { "K": "1" } }
            },
            "beats": [
                { "title": "b1", "compare": ["a", "b"], "scenario": ["action: X"],
                  "expect_per_variant": { "a": ["final: p = TRUE"], "b": ["final: p = FALSE"] } }
            ]
        }"#;
        let manifest = Manifest::parse(json).unwrap();
        let toml_str = manifest.to_toml().unwrap();
        let back: Manifest = toml::from_str(&toml_str).unwrap();
        back.validate().unwrap();
        assert_eq!(
            back.beats[0].compare,
            vec!["a".to_string(), "b".to_string()]
        );
        assert_eq!(back.beats[0].expect_per_variant.len(), 2);
        assert_eq!(back.variants["b"].constants["K"], "1".to_string());
    }
}
