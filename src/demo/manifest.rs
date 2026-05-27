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

impl Manifest {
    pub fn load(path: &Path) -> Result<Manifest, String> {
        let contents = std::fs::read_to_string(path)
            .map_err(|e| format!("failed to read manifest {}: {}", path.display(), e))?;
        Self::parse(&contents)
    }

    pub fn parse(contents: &str) -> Result<Manifest, String> {
        let manifest: Manifest =
            serde_json::from_str(contents).map_err(|e| format!("manifest parse error: {}", e))?;
        manifest.validate()?;
        Ok(manifest)
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).unwrap_or_default()
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
