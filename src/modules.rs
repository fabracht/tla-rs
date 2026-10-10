use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::ast::{DefinitionMap, Expr, InstanceDecl, Spec, UnparsedDefinition};
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

impl ModuleError {
    pub fn describe(&self, module: &str) -> String {
        match self {
            ModuleError::ParseError(message) => {
                format!("parse error in module {module}: {message}")
            }
            ModuleError::NotFound(_) => {
                format!("module {module} not found (no file {module}.tla in spec directory)")
            }
            ModuleError::CyclicDependency(dep) => format!("cyclic dependency loading module {dep}"),
            ModuleError::IoError(message) => {
                format!("I/O error loading module {module}: {message}")
            }
        }
    }
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

        let file: Arc<str> = file_path.display().to_string().into();
        let parsed = parser::parse(&content).map_err(|e| {
            let location = match e.span {
                Some(span) => {
                    let (line, column) = crate::source::Source::new(name.clone(), content.as_str())
                        .line_char_col(span.start);
                    format!("{file}:{line}:{column}")
                }
                None => file.to_string(),
            };
            ModuleError::ParseError(format!("{location}: {e}"))
        });

        self.loading_stack.pop();
        let mut spec = parsed?;
        for (_, body) in spec.definitions.values_mut() {
            if let Expr::Unparsed(unparsed) = body.as_ref() {
                let located = UnparsedDefinition {
                    file: Some(file.clone()),
                    ..unparsed.as_ref().clone()
                };
                *body = Arc::new(Expr::Unparsed(Arc::new(located)));
            }
        }
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

/// Adds the `VARIABLES`, `CONSTANTS` and definitions of the user modules `spec`
/// extends, transitively, as in the module TLC builds from the `EXTENDS` chain:
/// variables and constants ahead of its own, definitions under its own (a module's
/// definition overrides one it extends, the root's override all). A state is
/// indexed by `spec.vars`, and the cfg names definitions, so both must be complete
/// before the cfg is applied and the spec is checked. A module that does not parse is an error, so it is reported
/// before the cfg names a definition it was to provide; a module that cannot be
/// found or read is skipped here, and [`crate::checker::prepare_spec`] reports why.
///
/// An unnamed `INSTANCE M`, in the root or in a module it extends, brings in M's
/// definitions with its `WITH` substitutions applied. Each instantiation keeps its
/// own scope: its definitions are stored under keys of the form `M!Op#n`, and the
/// names inside them are rewritten to those keys, so a definition of the
/// instancing module never replaces one M relies on. M's definitions are then
/// added under their own names, except those of a `LOCAL INSTANCE` in an extended
/// module, which only the definitions of that module see. The standard modules
/// instanced modules depend on, and those that cannot be found or read, are added
/// to `spec.instances`, for [`crate::checker::prepare_spec`] to load or warn about.
pub fn merge_extended_declarations(spec: &mut Spec, spec_path: &Path) -> Result<(), String> {
    let mut resolver = InstanceResolver::new(spec_path);
    let mut visited = Vec::new();
    let mut declarations = Declarations::default();
    for module in &spec.extends {
        collect_declarations(module, &mut resolver, &mut visited, &mut declarations)?;
    }
    let imports = resolver.imports(&spec.instances, &mut Vec::new())?;
    declarations.import(&imports, imports.links.iter());
    declarations.add(&spec.vars, &spec.constants, &spec.definitions);
    spec.vars = declarations.vars;
    spec.constants = declarations.constants;
    spec.definitions = declarations.definitions;
    for module in resolver.deferred_modules {
        let loaded = spec.extends.contains(&module)
            || spec.instances.iter().any(|inst| inst.module_name == module);
        if !loaded {
            spec.instances.push(InstanceDecl {
                alias: None,
                params: Vec::new(),
                module_name: module,
                substitutions: Vec::new(),
                local: false,
            });
        }
    }
    Ok(())
}

#[derive(Default)]
struct Declarations {
    vars: Vec<Arc<str>>,
    constants: Vec<Arc<str>>,
    definitions: DefinitionMap,
}

impl Declarations {
    fn add(&mut self, vars: &[Arc<str>], constants: &[Arc<str>], definitions: &DefinitionMap) {
        for (name, definition) in definitions {
            self.definitions.insert(name.clone(), definition.clone());
        }
        for var in vars {
            if !self.vars.contains(var) {
                self.vars.push(var.clone());
            }
        }
        for constant in constants {
            if !self.constants.contains(constant) {
                self.constants.push(constant.clone());
            }
        }
    }

    fn import<'a>(&mut self, imports: &Imports, visible: impl Iterator<Item = &'a Link>) {
        self.definitions.extend(imports.scoped.clone());
        for link in visible {
            if let Some(definition) = imports.scoped.get(&link.key) {
                self.definitions
                    .insert(link.name.clone(), definition.clone());
            }
        }
    }
}

fn collect_declarations(
    name: &Arc<str>,
    resolver: &mut InstanceResolver,
    visited: &mut Vec<Arc<str>>,
    declarations: &mut Declarations,
) -> Result<(), String> {
    if crate::stdlib::is_stdlib_module(name) || visited.contains(name) {
        return Ok(());
    }
    visited.push(name.clone());
    let module = match resolver.registry.load(name, &resolver.spec_path) {
        Ok(module) => module,
        Err(error @ ModuleError::ParseError(_)) => return Err(error.describe(name)),
        Err(_) => return Ok(()),
    };
    let (extends, instances, vars, constants, definitions) = (
        module.extends.clone(),
        module.instances.clone(),
        module.vars.clone(),
        module.constants.clone(),
        module.definitions.clone(),
    );
    for inner in &extends {
        collect_declarations(inner, resolver, visited, declarations)?;
    }
    let imports = resolver.imports(&instances, &mut Vec::new())?;
    declarations.import(&imports, imports.links.iter().filter(|link| !link.local));
    let local_links: Vec<&Link> = imports.links.iter().filter(|link| link.local).collect();
    declarations.add(
        &vars,
        &constants,
        &rename(&definitions, local_links.into_iter()),
    );
    Ok(())
}

/// A name a module sees through an unnamed `INSTANCE`, and the key of the
/// definition it stands for.
#[derive(Clone)]
struct Link {
    name: Arc<str>,
    key: Arc<str>,
    local: bool,
}

/// What a module's unnamed `INSTANCE`s bring in: the names it sees, and the
/// definitions behind them under their keys.
#[derive(Default)]
struct Imports {
    links: Vec<Link>,
    scoped: DefinitionMap,
}

struct InstanceResolver {
    registry: ModuleRegistry,
    spec_path: PathBuf,
    copies: usize,
    deferred_modules: Vec<Arc<str>>,
}

impl InstanceResolver {
    fn new(spec_path: &Path) -> Self {
        Self {
            registry: ModuleRegistry::new(),
            spec_path: spec_path.to_path_buf(),
            copies: 0,
            deferred_modules: Vec::new(),
        }
    }

    fn defer(&mut self, module: &Arc<str>) {
        if !self.deferred_modules.contains(module) {
            self.deferred_modules.push(module.clone());
        }
    }

    fn imports(
        &mut self,
        instances: &[InstanceDecl],
        loading: &mut Vec<Arc<str>>,
    ) -> Result<Imports, String> {
        let mut imports = Imports::default();
        for inst in instances.iter().filter(|inst| inst.alias.is_none()) {
            if crate::stdlib::is_stdlib_module(&inst.module_name) {
                self.defer(&inst.module_name);
                continue;
            }
            let Some(instance) =
                self.instantiate(&inst.module_name, &inst.substitutions, loading)?
            else {
                continue;
            };
            imports.scoped.extend(instance.scoped);
            imports
                .links
                .extend(instance.links.into_iter().map(|link| Link {
                    local: inst.local,
                    ..link
                }));
        }
        Ok(imports)
    }

    /// Module `name` instanced with `substitutions`: the names it exports, linked
    /// to its definitions under fresh keys, together with the definitions of the
    /// modules it extends and instances, all rewritten so that every name refers
    /// to the definition in scope where it was written. `None` when the module
    /// cannot be found or read.
    fn instantiate(
        &mut self,
        name: &Arc<str>,
        substitutions: &[(Arc<str>, Expr)],
        loading: &mut Vec<Arc<str>>,
    ) -> Result<Option<Imports>, String> {
        if loading.contains(name) {
            return Err(ModuleError::CyclicDependency(name.clone()).describe(name));
        }
        let module = match self.registry.load(name, &self.spec_path) {
            Ok(module) => module,
            Err(error @ ModuleError::ParseError(_)) => return Err(error.describe(name)),
            Err(_) => {
                self.defer(name);
                return Ok(None);
            }
        };
        let (extends, instances, definitions) = (
            module.extends.clone(),
            module.instances.clone(),
            module.definitions.clone(),
        );
        loading.push(name.clone());
        let mut inner = Imports::default();
        for extended in &extends {
            if crate::stdlib::is_stdlib_module(extended) {
                self.defer(extended);
            } else if let Some(instance) = self.instantiate(extended, &[], loading)? {
                inner.scoped.extend(instance.scoped);
                inner.links.extend(instance.links);
            }
        }
        let imports = self.imports(&instances, loading)?;
        inner.scoped.extend(imports.scoped);
        inner.links.extend(imports.links);
        loading.pop();

        let copy = self.copies;
        self.copies += 1;
        let own_links: Vec<Link> = definitions
            .keys()
            .map(|op| Link {
                name: op.clone(),
                key: format!("{name}!{op}#{copy}").into(),
                local: false,
            })
            .collect();
        let in_scope: Vec<&Link> = inner
            .links
            .iter()
            .filter(|link| !definitions.contains_key(&link.name))
            .chain(own_links.iter())
            .collect();
        let renamings: Vec<(Arc<str>, Expr)> = substitutions
            .iter()
            .cloned()
            .chain(
                in_scope
                    .iter()
                    .map(|link| (link.name.clone(), Expr::Var(link.key.clone()))),
            )
            .collect();
        let mut scoped = substitute_definitions(&inner.scoped, &renamings);
        let own = substitute_definitions(&definitions, &renamings);
        for link in &own_links {
            if let Some(definition) = own.get(&link.name) {
                scoped.insert(link.key.clone(), definition.clone());
            }
        }
        let links = in_scope
            .into_iter()
            .filter(|link| !link.local)
            .cloned()
            .collect();
        Ok(Some(Imports { links, scoped }))
    }
}

fn rename<'a>(definitions: &DefinitionMap, links: impl Iterator<Item = &'a Link>) -> DefinitionMap {
    let renamings: Vec<(Arc<str>, Expr)> = links
        .filter(|link| !definitions.contains_key(&link.name))
        .map(|link| (link.name.clone(), Expr::Var(link.key.clone())))
        .collect();
    substitute_definitions(definitions, &renamings)
}

/// `definitions` with `substitutions` applied to each body, except for the names
/// its parameters bind.
fn substitute_definitions(
    definitions: &DefinitionMap,
    substitutions: &[(Arc<str>, Expr)],
) -> DefinitionMap {
    if substitutions.is_empty() {
        return definitions.clone();
    }
    definitions
        .iter()
        .map(|(name, (params, body))| {
            let free: Vec<(Arc<str>, Expr)> = substitutions
                .iter()
                .filter(|(target, _)| !params.contains(target))
                .cloned()
                .collect();
            let body = crate::substitution::substitute_expr(body, &free);
            (name.clone(), (params.clone(), Arc::new(body)))
        })
        .collect()
}

type InstanceVars = BTreeMap<Arc<str>, Vec<Arc<str>>>;
type ResolvedInstances = (
    BTreeMap<Arc<str>, Definitions>,
    ParameterizedInstances,
    InstanceVars,
);

pub fn resolve_instances(
    spec: &Spec,
    registry: &ModuleRegistry,
) -> std::result::Result<ResolvedInstances, ModuleError> {
    let mut resolved = BTreeMap::new();
    let mut parameterized = BTreeMap::new();
    let mut instance_vars = BTreeMap::new();

    for inst in &spec.instances {
        let alias = match &inst.alias {
            Some(a) => a.clone(),
            None => inst.module_name.clone(),
        };

        if let Some(module) = registry.get(&inst.module_name) {
            if inst.params.is_empty() {
                let substituted = apply_substitutions(&module.definitions, &inst.substitutions);
                resolved.insert(alias.clone(), substituted);
                instance_vars.insert(alias, module.vars.clone());
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

    Ok((resolved, parameterized, instance_vars))
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
    fn a_module_definition_that_fails_to_parse_is_recorded_with_its_file() {
        let dir = std::env::temp_dir().join("tlc_test_module_unparsed_definition");
        let _ = std::fs::create_dir_all(&dir);
        let tla_path = dir.join("BrokenDef.tla");
        std::fs::write(
            &tla_path,
            "---- MODULE BrokenDef ----\nGood == 1\nBad == [a/b |-> 1]\n====\n",
        )
        .expect("write module");

        let mut reg = ModuleRegistry::new();
        let loaded = reg
            .load("BrokenDef", &dir.join("base.tla"))
            .map(|module| module.unparsed_definition("Bad").cloned());
        let _ = std::fs::remove_dir_all(&dir);

        let bad = match loaded {
            Ok(Some(bad)) => bad,
            Ok(None) => panic!("`Bad` should be recorded as unparsed"),
            Err(error) => panic!("the module should load: {error:?}"),
        };
        let file = tla_path.display().to_string();
        assert_eq!(bad.file.as_deref(), Some(file.as_str()));
        assert_eq!((bad.line, bad.column), (3, 13));
    }

    #[test]
    fn a_module_that_does_not_parse_reports_its_file_and_line() {
        let dir = std::env::temp_dir().join("tlc_test_module_parse_error");
        let _ = std::fs::create_dir_all(&dir);
        let tla_path = dir.join("Garbage.tla");
        std::fs::write(
            &tla_path,
            "---- MODULE Garbage ----\nthis is not TLA+\nGood == 1\n====\n",
        )
        .expect("write module");

        let base = dir.join("base.tla");
        let mut reg = ModuleRegistry::new();
        let first = reg.load("Garbage", &base).map(|_| ());
        let second = reg.load("Garbage", &base).map(|_| ());
        let _ = std::fs::remove_dir_all(&dir);

        let expected_location = format!("{}:2:6", tla_path.display());
        match first {
            Err(ModuleError::ParseError(message)) => {
                assert!(message.starts_with(&expected_location), "{message}");
            }
            other => panic!("expected a parse error, got {other:?}"),
        }
        assert!(
            matches!(second, Err(ModuleError::ParseError(_))),
            "loading again after a parse error must not report a cycle: {second:?}"
        );
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
                Expr::Add(Box::new(var_expr("N")), Box::new(lit_int(1))).into(),
            ),
        );
        module_defs.insert(
            var("Helper"),
            (
                vec![var("x")],
                Expr::Mul(Box::new(var_expr("x")), Box::new(var_expr("N"))).into(),
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
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
            constant_substitutions: Vec::new(),
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
                    local: false,
                },
                InstanceDecl {
                    alias: Some(Arc::from("P")),
                    params: vec![var("n")],
                    module_name: Arc::from("TestMod"),
                    substitutions: vec![(var("N"), var_expr("n"))],
                    local: false,
                },
            ],
            init: None,
            next: None,
            invariants: vec![],
            invariant_names: vec![],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
            constant_substitutions: Vec::new(),
        };

        let (resolved, parameterized, _vars) = resolve_instances(&spec, &registry).unwrap();

        assert_eq!(resolved.len(), 1);
        let s_defs = resolved.get(&Arc::from("S") as &Arc<str>).unwrap();
        let (_, op_body) = s_defs.get(&var("Op")).unwrap();
        assert_eq!(
            **op_body,
            Expr::Add(Box::new(lit_int(5)), Box::new(lit_int(1)))
        );
        let (params, helper_body) = s_defs.get(&var("Helper")).unwrap();
        assert_eq!(params, &vec![var("x")]);
        assert_eq!(
            **helper_body,
            Expr::Mul(Box::new(var_expr("x")), Box::new(lit_int(5)))
        );

        assert_eq!(parameterized.len(), 1);
        let p_inst = parameterized.get(&Arc::from("P") as &Arc<str>).unwrap();
        assert_eq!(p_inst.params, vec![var("n")]);
        assert_eq!(p_inst.substitutions.len(), 1);
    }
}
