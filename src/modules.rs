use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::ast::{Expr, Spec};
use crate::eval::{Definitions, ParameterizedInstance, ParameterizedInstances};
use crate::parser;

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

pub fn apply_substitutions(module_defs: &Definitions, subs: &[(Arc<str>, Expr)]) -> Definitions {
    let mut result = BTreeMap::new();
    for (name, (params, body)) in module_defs {
        let new_body = substitute_expr(body, subs);
        result.insert(name.clone(), (params.clone(), new_body));
    }
    result
}

fn prime_expr(expr: &Expr) -> Expr {
    match expr {
        Expr::Var(name) => Expr::Prime(name.clone()),
        Expr::FnApp(f, arg) => Expr::FnApp(Box::new(prime_expr(f)), Box::new(prime_expr(arg))),
        Expr::RecordAccess(r, field) => Expr::RecordAccess(Box::new(prime_expr(r)), field.clone()),
        Expr::TupleAccess(t, idx) => Expr::TupleAccess(Box::new(prime_expr(t)), *idx),
        other => other.clone(),
    }
}

pub fn substitute_expr(expr: &Expr, subs: &[(Arc<str>, Expr)]) -> Expr {
    match expr {
        Expr::Var(name) => {
            for (param, replacement) in subs {
                if param == name {
                    return replacement.clone();
                }
            }
            Expr::Var(name.clone())
        }

        Expr::And(l, r) => Expr::And(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Or(l, r) => Expr::Or(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Not(e) => Expr::Not(Box::new(substitute_expr(e, subs))),
        Expr::Implies(l, r) => Expr::Implies(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Equiv(l, r) => Expr::Equiv(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Eq(l, r) => Expr::Eq(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Neq(l, r) => Expr::Neq(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::In(l, r) => Expr::In(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::NotIn(l, r) => Expr::NotIn(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),

        Expr::Add(l, r) => Expr::Add(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Sub(l, r) => Expr::Sub(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Mul(l, r) => Expr::Mul(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Div(l, r) => Expr::Div(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Mod(l, r) => Expr::Mod(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Exp(l, r) => Expr::Exp(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Neg(e) => Expr::Neg(Box::new(substitute_expr(e, subs))),
        Expr::BitwiseAnd(l, r) => Expr::BitwiseAnd(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::TransitiveClosure(e) => Expr::TransitiveClosure(Box::new(substitute_expr(e, subs))),
        Expr::ReflexiveTransitiveClosure(e) => {
            Expr::ReflexiveTransitiveClosure(Box::new(substitute_expr(e, subs)))
        }
        Expr::ActionCompose(l, r) => Expr::ActionCompose(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Lt(l, r) => Expr::Lt(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Le(l, r) => Expr::Le(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Gt(l, r) => Expr::Gt(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Ge(l, r) => Expr::Ge(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),

        Expr::SetEnum(elems) => {
            Expr::SetEnum(elems.iter().map(|e| substitute_expr(e, subs)).collect())
        }
        Expr::SetRange(l, r) => Expr::SetRange(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::SetFilter(var, domain, pred) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::SetFilter(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(pred, &filtered_subs)),
            )
        }
        Expr::SetMap(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::SetMap(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::Union(l, r) => Expr::Union(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Intersect(l, r) => Expr::Intersect(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::SetMinus(l, r) => Expr::SetMinus(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Cartesian(l, r) => Expr::Cartesian(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Subset(l, r) => Expr::Subset(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::ProperSubset(l, r) => Expr::ProperSubset(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Powerset(e) => Expr::Powerset(Box::new(substitute_expr(e, subs))),
        Expr::Cardinality(e) => Expr::Cardinality(Box::new(substitute_expr(e, subs))),
        Expr::IsFiniteSet(e) => Expr::IsFiniteSet(Box::new(substitute_expr(e, subs))),
        Expr::BigUnion(e) => Expr::BigUnion(Box::new(substitute_expr(e, subs))),

        Expr::Exists(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::Exists(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::Forall(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::Forall(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::Choose(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::Choose(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }

        Expr::FnApp(f, arg) => Expr::FnApp(
            Box::new(substitute_expr(f, subs)),
            Box::new(substitute_expr(arg, subs)),
        ),
        Expr::FnDef(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::FnDef(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::FnCall(name, args) => Expr::FnCall(
            name.clone(),
            args.iter().map(|a| substitute_expr(a, subs)).collect(),
        ),
        Expr::Lambda(params, body) => {
            let filtered_subs: Vec<_> = subs
                .iter()
                .filter(|(p, _)| !params.contains(p))
                .cloned()
                .collect();
            Expr::Lambda(
                params.clone(),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::FnMerge(l, r) => Expr::FnMerge(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::SingleFn(l, r) => Expr::SingleFn(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::CustomOp(name, l, r) => Expr::CustomOp(
            name.clone(),
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Except(base, updates) => {
            let new_updates: Vec<_> = updates
                .iter()
                .map(|(keys, val)| {
                    let new_keys: Vec<_> = keys.iter().map(|k| substitute_expr(k, subs)).collect();
                    (new_keys, substitute_expr(val, subs))
                })
                .collect();
            Expr::Except(Box::new(substitute_expr(base, subs)), new_updates)
        }
        Expr::Domain(e) => Expr::Domain(Box::new(substitute_expr(e, subs))),
        Expr::FunctionSet(l, r) => Expr::FunctionSet(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),

        Expr::RecordLit(fields) => Expr::RecordLit(
            fields
                .iter()
                .map(|(name, val)| (name.clone(), substitute_expr(val, subs)))
                .collect(),
        ),
        Expr::RecordSet(fields) => Expr::RecordSet(
            fields
                .iter()
                .map(|(name, val)| (name.clone(), substitute_expr(val, subs)))
                .collect(),
        ),
        Expr::RecordAccess(rec, field) => {
            Expr::RecordAccess(Box::new(substitute_expr(rec, subs)), field.clone())
        }

        Expr::TupleLit(elems) => {
            Expr::TupleLit(elems.iter().map(|e| substitute_expr(e, subs)).collect())
        }
        Expr::TupleAccess(tup, idx) => {
            Expr::TupleAccess(Box::new(substitute_expr(tup, subs)), *idx)
        }

        Expr::Len(e) => Expr::Len(Box::new(substitute_expr(e, subs))),
        Expr::Head(e) => Expr::Head(Box::new(substitute_expr(e, subs))),
        Expr::Tail(e) => Expr::Tail(Box::new(substitute_expr(e, subs))),
        Expr::Append(l, r) => Expr::Append(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Concat(l, r) => Expr::Concat(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::SubSeq(seq, start, end) => Expr::SubSeq(
            Box::new(substitute_expr(seq, subs)),
            Box::new(substitute_expr(start, subs)),
            Box::new(substitute_expr(end, subs)),
        ),
        Expr::SelectSeq(seq, test) => Expr::SelectSeq(
            Box::new(substitute_expr(seq, subs)),
            Box::new(substitute_expr(test, subs)),
        ),
        Expr::SeqSet(e) => Expr::SeqSet(Box::new(substitute_expr(e, subs))),

        Expr::If(cond, then_br, else_br) => Expr::If(
            Box::new(substitute_expr(cond, subs)),
            Box::new(substitute_expr(then_br, subs)),
            Box::new(substitute_expr(else_br, subs)),
        ),
        Expr::Let(var, binding, body) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::Let(
                var.clone(),
                Box::new(substitute_expr(binding, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::Case(branches) => Expr::Case(
            branches
                .iter()
                .map(|(cond, result)| (substitute_expr(cond, subs), substitute_expr(result, subs)))
                .collect(),
        ),

        Expr::Unchanged(vars) => Expr::Unchanged(vars.clone()),
        Expr::Prime(var) => {
            for (param, replacement) in subs {
                if param == var {
                    return prime_expr(replacement);
                }
            }
            Expr::Prime(var.clone())
        }

        Expr::Always(e) => Expr::Always(Box::new(substitute_expr(e, subs))),
        Expr::Eventually(e) => Expr::Eventually(Box::new(substitute_expr(e, subs))),
        Expr::LeadsTo(l, r) => Expr::LeadsTo(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::WeakFairness(var, action) => {
            Expr::WeakFairness(var.clone(), Box::new(substitute_expr(action, subs)))
        }
        Expr::StrongFairness(var, action) => {
            Expr::StrongFairness(var.clone(), Box::new(substitute_expr(action, subs)))
        }
        Expr::BoxAction(action, var) => {
            Expr::BoxAction(Box::new(substitute_expr(action, subs)), var.clone())
        }
        Expr::DiamondAction(action, var) => {
            Expr::DiamondAction(Box::new(substitute_expr(action, subs)), var.clone())
        }
        Expr::EnabledOp(e) => Expr::EnabledOp(Box::new(substitute_expr(e, subs))),

        Expr::QualifiedCall(inst, op, args) => Expr::QualifiedCall(
            Box::new(substitute_expr(inst, subs)),
            op.clone(),
            args.iter().map(|a| substitute_expr(a, subs)).collect(),
        ),

        Expr::LabeledAction(label, action) => {
            Expr::LabeledAction(label.clone(), Box::new(substitute_expr(action, subs)))
        }

        Expr::Lit(_)
        | Expr::OldValue
        | Expr::Print(_, _)
        | Expr::PrintT(_)
        | Expr::Assert(_, _)
        | Expr::JavaTime
        | Expr::SystemTime
        | Expr::Permutations(_)
        | Expr::SortSeq(_, _)
        | Expr::TLCToString(_)
        | Expr::RandomElement(_)
        | Expr::TLCGet(_)
        | Expr::TLCSet(_, _)
        | Expr::Any
        | Expr::TLCEval(_)
        | Expr::IsABag(_)
        | Expr::BagToSet(_)
        | Expr::SetToBag(_)
        | Expr::BagIn(_, _)
        | Expr::EmptyBag
        | Expr::BagAdd(_, _)
        | Expr::BagSub(_, _)
        | Expr::BagUnion(_)
        | Expr::SqSubseteq(_, _)
        | Expr::SubBag(_)
        | Expr::BagOfAll(_, _)
        | Expr::BagCardinality(_)
        | Expr::CopiesIn(_, _) => expr.clone(),
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
    use crate::ast::Value;
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
    fn substitute_var_matches() {
        let subs = vec![(var("x"), lit_int(42))];
        let result = substitute_expr(&var_expr("x"), &subs);
        assert_eq!(result, lit_int(42));
    }

    #[test]
    fn substitute_var_no_match() {
        let subs = vec![(var("x"), lit_int(42))];
        let result = substitute_expr(&var_expr("y"), &subs);
        assert_eq!(result, var_expr("y"));
    }

    #[test]
    fn substitute_nested_and() {
        let subs = vec![(var("a"), lit_int(1))];
        let expr = Expr::And(
            Box::new(Expr::Eq(Box::new(var_expr("a")), Box::new(lit_int(0)))),
            Box::new(var_expr("b")),
        );
        let result = substitute_expr(&expr, &subs);
        let expected = Expr::And(
            Box::new(Expr::Eq(Box::new(lit_int(1)), Box::new(lit_int(0)))),
            Box::new(var_expr("b")),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn substitute_respects_binding_scope() {
        let subs = vec![(var("x"), lit_int(99))];
        let expr = Expr::Exists(
            var("x"),
            Box::new(Expr::SetEnum(vec![lit_int(1), lit_int(2)])),
            Box::new(Expr::Eq(Box::new(var_expr("x")), Box::new(lit_int(1)))),
        );
        let result = substitute_expr(&expr, &subs);
        if let Expr::Exists(_, _, body) = &result {
            assert_eq!(
                **body,
                Expr::Eq(Box::new(var_expr("x")), Box::new(lit_int(1)))
            );
        } else {
            panic!("expected Exists");
        }
    }

    #[test]
    fn substitute_let_binding_scope() {
        let subs = vec![(var("x"), lit_int(99))];
        let expr = Expr::Let(var("x"), Box::new(lit_int(5)), Box::new(var_expr("x")));
        let result = substitute_expr(&expr, &subs);
        if let Expr::Let(_, binding, body) = &result {
            assert_eq!(**binding, lit_int(5));
            assert_eq!(**body, var_expr("x"));
        } else {
            panic!("expected Let");
        }
    }

    #[test]
    fn apply_substitutions_replaces_in_defs() {
        let mut defs: Definitions = BTreeMap::new();
        defs.insert(
            var("Op"),
            (
                vec![],
                Expr::Add(Box::new(var_expr("N")), Box::new(lit_int(1))),
            ),
        );
        let subs = vec![(var("N"), lit_int(10))];
        let result = apply_substitutions(&defs, &subs);
        let (_, body) = result.get(&var("Op")).expect("Op should exist");
        assert_eq!(
            *body,
            Expr::Add(Box::new(lit_int(10)), Box::new(lit_int(1)))
        );
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
    fn substitute_literal_unchanged() {
        let subs = vec![(var("x"), var_expr("y"))];
        let result = substitute_expr(&lit_int(42), &subs);
        assert_eq!(result, lit_int(42));
    }

    #[test]
    fn substitute_if_then_else() {
        let subs = vec![(var("c"), Expr::Lit(Value::Bool(true)))];
        let expr = Expr::If(
            Box::new(var_expr("c")),
            Box::new(lit_int(1)),
            Box::new(lit_int(2)),
        );
        let result = substitute_expr(&expr, &subs);
        let expected = Expr::If(
            Box::new(Expr::Lit(Value::Bool(true))),
            Box::new(lit_int(1)),
            Box::new(lit_int(2)),
        );
        assert_eq!(result, expected);
    }
}
