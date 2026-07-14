use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::Source;
use crate::ast::{Env, Spec, Value};
use crate::checker::CheckerConfig;
use crate::config::{apply_config, parse_cfg};
use crate::parser::parse_with_warnings;
use crate::span::{Span, Spanned};

pub struct Prepared {
    pub spec: Spec,
    pub source: Source,
    pub domains: Env,
    pub spec_path: PathBuf,
    pub checker_config: CheckerConfig,
    pub warnings: Vec<Spanned<String>>,
}

#[derive(Debug)]
pub enum PrepareError {
    Io(String),
    Parse { message: String, span: Option<Span> },
    Config(String),
}

impl std::fmt::Display for PrepareError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrepareError::Io(m) | PrepareError::Config(m) => write!(f, "{}", m),
            PrepareError::Parse { message, .. } => write!(f, "{}", message),
        }
    }
}

impl std::error::Error for PrepareError {}

pub fn prepare_from_path(
    spec_path: &Path,
    config_path: Option<&Path>,
    constants: &[(Arc<str>, Value)],
) -> Result<Prepared, PrepareError> {
    let contents = fs::read_to_string(spec_path)
        .map_err(|e| PrepareError::Io(format!("failed to read {}: {}", spec_path.display(), e)))?;
    let source = Source::new(spec_path.display().to_string(), contents.clone());

    let (mut spec, mut warnings) =
        parse_with_warnings(&contents).map_err(|err| PrepareError::Parse {
            message: err.message.clone(),
            span: err.span,
        })?;

    let mut domains = Env::new();
    let mut checker_config = CheckerConfig {
        spec_path: Some(spec_path.to_path_buf()),
        quiet: true,
        ..CheckerConfig::default()
    };

    let auto_cfg = spec_path.with_extension("cfg");
    let cfg_path = match config_path {
        Some(p) => Some(p.to_path_buf()),
        None if auto_cfg.exists() => Some(auto_cfg),
        _ => None,
    };

    if let Some(cfg) = cfg_path {
        let cfg_contents = fs::read_to_string(&cfg).map_err(|e| {
            PrepareError::Config(format!("failed to read cfg {}: {}", cfg.display(), e))
        })?;
        let cfg_parsed = parse_cfg(&cfg_contents)
            .map_err(|e| PrepareError::Config(format!("cfg parse error: {}", e)))?;
        let cfg_warnings = apply_config(
            &cfg_parsed,
            &mut spec,
            &mut domains,
            &mut checker_config,
            constants,
            &[],
            false,
        )
        .map_err(|e| PrepareError::Config(format!("cfg apply error: {}", e)))?;
        warnings.extend(
            cfg_warnings
                .into_iter()
                .map(|w| Spanned::new(w, Span::default())),
        );
    }

    for (name, value) in constants {
        domains.insert(name.clone(), value.clone());
    }

    Ok(Prepared {
        spec,
        source,
        domains,
        spec_path: spec_path.to_path_buf(),
        checker_config,
        warnings,
    })
}
