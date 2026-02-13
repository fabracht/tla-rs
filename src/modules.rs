use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::ast::Spec;
use crate::eval::{Definitions, ParameterizedInstance, ParameterizedInstances};
use crate::parser;
use crate::substitution::apply_substitutions;

#[derive(Debug)]
pub enum ModuleError {
    NotFound(Arc<str>),
    ParseError(String),
    CyclicDependency(Arc<str>),
    IoError(String),
}

pub struct ModuleRegistry {
    modules: BTreeMap<Arc<str>, Spec>,
    search_paths: Vec<PathBuf>,
    loading_stack: Vec<Arc<str>>,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self {
            modules: BTreeMap::new(),
            search_paths: Vec::new(),
            loading_stack: Vec::new(),
        }
    }

    pub fn add_search_path(&mut self, path: PathBuf) {
        self.search_paths.push(path);
    }

    pub fn load(&mut self, name: &str, base_path: &Path) -> Result<&Spec, ModuleError> {
        let name: Arc<str> = name.into();

        if self.loading_stack.contains(&name) {
            return Err(ModuleError::CyclicDependency(name));
        }

        if self.modules.contains_key(&name) {
            return self.modules.get(&name).ok_or(ModuleError::NotFound(name));
        }

        let file_path = self.find_module(&name, base_path)?;
        let content = std::fs::read_to_string(&file_path)
            .map_err(|e| ModuleError::IoError(format!("{}: {}", file_path.display(), e)))?;

        self.loading_stack.push(name.clone());

        let spec = parser::parse(&content)
            .map_err(|e| ModuleError::ParseError(format!("{}: {}", name, e.message)))?;

        self.loading_stack.pop();
        self.modules.insert(name.clone(), spec);
        self.modules.get(&name).ok_or(ModuleError::NotFound(name))
    }

    fn find_module(&self, name: &str, base_path: &Path) -> Result<PathBuf, ModuleError> {
        let filename = format!("{}.tla", name);
        let base_dir = base_path.parent().unwrap_or(Path::new("."));
        let candidate = base_dir.join(&filename);
        if candidate.exists() {
            return Ok(candidate);
        }

        for search_path in &self.search_paths {
            let candidate = search_path.join(&filename);
            if candidate.exists() {
                return Ok(candidate);
            }
        }

        Err(ModuleError::NotFound(name.into()))
    }

    pub fn get(&self, name: &str) -> Option<&Spec> {
        self.modules.get(name)
    }
}

impl Default for ModuleRegistry {
    fn default() -> Self {
        Self::new()
    }
}

pub fn resolve_instances(
    spec: &Spec,
    registry: &ModuleRegistry,
) -> std::result::Result<(BTreeMap<Arc<str>, Definitions>, ParameterizedInstances), ModuleError> {
    let mut resolved = BTreeMap::new();
    let mut parameterized = BTreeMap::new();

    for inst in &spec.instances {
        let alias = match &inst.alias {
            Some(a) => a.clone(),
            None => inst.module_name.clone(),
        };

        if let Some(module) = registry.get(&inst.module_name) {
            if inst.params.is_empty() {
                let substituted = apply_substitutions(&module.definitions, &inst.substitutions);
                resolved.insert(alias, substituted);
            } else {
                parameterized.insert(
                    alias,
                    ParameterizedInstance {
                        params: inst.params.clone(),
                        module_defs: module.definitions.clone(),
                        substitutions: inst.substitutions.clone(),
                    },
                );
            }
        }
    }

    Ok((resolved, parameterized))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expr, Value};
    use std::io::Write;

    fn var(name: &str) -> Arc<str> {
        Arc::from(name)
    }

    fn var_expr(name: &str) -> Expr {
        Expr::Var(var(name))
    }

    fn lit_int(n: i64) -> Expr {
        Expr::Lit(Value::Int(n))
    }

    #[test]
    fn registry_new_is_empty() {
        let reg = ModuleRegistry::new();
        assert!(reg.get("anything").is_none());
    }

    #[test]
    fn registry_default_is_empty() {
        let reg = ModuleRegistry::default();
        assert!(reg.get("anything").is_none());
    }

    #[test]
    fn load_nonexistent_module() {
        let mut reg = ModuleRegistry::new();
        let result = reg.load("NonExistentModule", Path::new("/tmp/fake.tla"));
        assert!(matches!(result, Err(ModuleError::NotFound(_))));
    }

    #[test]
    fn load_and_cache_module() {
        let dir = std::env::temp_dir().join("tlc_test_load_cache");
        let _ = std::fs::create_dir_all(&dir);
        let tla_path = dir.join("TestMod.tla");
        let mut f = std::fs::File::create(&tla_path).expect("create file");
        writeln!(f, "---- MODULE TestMod ----").ok();
        writeln!(f, "VARIABLES x").ok();
        writeln!(f, "Init == x = 0").ok();
        writeln!(f, "Next == x' = x + 1").ok();
        writeln!(f, "====").ok();
        drop(f);

        let base = dir.join("base.tla");
        let mut reg = ModuleRegistry::new();
        let spec1 = reg.load("TestMod", &base);
        assert!(spec1.is_ok());
        assert_eq!(spec1.unwrap().vars.len(), 1);

        let spec2 = reg.get("TestMod");
        assert!(spec2.is_some());

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn search_path_resolution() {
        let dir = std::env::temp_dir().join("tlc_test_search_path");
        let search_dir = dir.join("libs");
        let _ = std::fs::create_dir_all(&search_dir);
        let tla_path = search_dir.join("SearchMod.tla");
        let mut f = std::fs::File::create(&tla_path).expect("create file");
        writeln!(f, "---- MODULE SearchMod ----").ok();
        writeln!(f, "VARIABLES y").ok();
        writeln!(f, "Init == y = 1").ok();
        writeln!(f, "Next == y' = y").ok();
        writeln!(f, "====").ok();
        drop(f);

        let mut reg = ModuleRegistry::new();
        reg.add_search_path(search_dir);
        let result = reg.load("SearchMod", Path::new("/tmp/other.tla"));
        assert!(result.is_ok());

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn cyclic_dependency_detected() {
        let mut reg = ModuleRegistry::new();
        reg.loading_stack.push(var("CyclicMod"));
        let result = reg.load("CyclicMod", Path::new("/tmp/fake.tla"));
        assert!(matches!(result, Err(ModuleError::CyclicDependency(_))));
        reg.loading_stack.pop();
    }

    #[test]
    fn resolve_instances_static_and_parameterized() {
        use crate::ast::InstanceDecl;

        let mut module_defs: Definitions = BTreeMap::new();
        module_defs.insert(
            var("Op"),
            (
                vec![],
                Expr::Add(Box::new(var_expr("N")), Box::new(lit_int(1))),
            ),
        );
        module_defs.insert(
            var("Helper"),
            (
                vec![var("x")],
                Expr::Mul(Box::new(var_expr("x")), Box::new(var_expr("N"))),
            ),
        );

        let module_spec = Spec {
            vars: vec![],
            constants: vec![var("N")],
            extends: vec![],
            definitions: module_defs,
            assumes: vec![],
            instances: vec![],
            init: None,
            next: None,
            invariants: vec![],
            invariant_names: vec![],
            fairness: vec![],
            liveness_properties: vec![],
        };

        let mut registry = ModuleRegistry::new();
        registry.modules.insert(Arc::from("TestMod"), module_spec);

        let spec = Spec {
            vars: vec![var("x")],
            constants: vec![],
            extends: vec![],
            definitions: BTreeMap::new(),
            assumes: vec![],
            instances: vec![
                InstanceDecl {
                    alias: Some(Arc::from("S")),
                    params: vec![],
                    module_name: Arc::from("TestMod"),
                    substitutions: vec![(var("N"), lit_int(5))],
                },
                InstanceDecl {
                    alias: Some(Arc::from("P")),
                    params: vec![var("n")],
                    module_name: Arc::from("TestMod"),
                    substitutions: vec![(var("N"), var_expr("n"))],
                },
            ],
            init: None,
            next: None,
            invariants: vec![],
            invariant_names: vec![],
            fairness: vec![],
            liveness_properties: vec![],
        };

        let (resolved, parameterized) = resolve_instances(&spec, &registry).unwrap();

        assert_eq!(resolved.len(), 1);
        let s_defs = resolved.get(&Arc::from("S") as &Arc<str>).unwrap();
        let (_, op_body) = s_defs.get(&var("Op")).unwrap();
        assert_eq!(
            *op_body,
            Expr::Add(Box::new(lit_int(5)), Box::new(lit_int(1)))
        );
        let (params, helper_body) = s_defs.get(&var("Helper")).unwrap();
        assert_eq!(params, &vec![var("x")]);
        assert_eq!(
            *helper_body,
            Expr::Mul(Box::new(var_expr("x")), Box::new(lit_int(5)))
        );

        assert_eq!(parameterized.len(), 1);
        let p_inst = parameterized.get(&Arc::from("P") as &Arc<str>).unwrap();
        assert_eq!(p_inst.params, vec![var("n")]);
        assert_eq!(p_inst.substitutions.len(), 1);
    }
}
