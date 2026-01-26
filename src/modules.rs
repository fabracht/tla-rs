use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::ast::{Expr, Spec};
use crate::eval::Definitions;
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
            return Ok(self.modules.get(&name).unwrap());
        }

        let file_path = self.find_module(&name, base_path)?;
        let content = std::fs::read_to_string(&file_path)
            .map_err(|e| ModuleError::IoError(format!("{}: {}", file_path.display(), e)))?;

        self.loading_stack.push(name.clone());

        let spec = parser::parse(&content)
            .map_err(|e| ModuleError::ParseError(format!("{}: {}", name, e.message)))?;

        self.loading_stack.pop();
        self.modules.insert(name.clone(), spec);

        Ok(self.modules.get(&name).unwrap())
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

pub fn apply_substitutions(
    module_defs: &Definitions,
    subs: &[(Arc<str>, Expr)],
) -> Definitions {
    let mut result = BTreeMap::new();
    for (name, (params, body)) in module_defs {
        let new_body = substitute_expr(body, subs);
        result.insert(name.clone(), (params.clone(), new_body));
    }
    result
}

fn substitute_expr(expr: &Expr, subs: &[(Arc<str>, Expr)]) -> Expr {
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
        Expr::ReflexiveTransitiveClosure(e) => Expr::ReflexiveTransitiveClosure(Box::new(substitute_expr(e, subs))),
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

        Expr::SetEnum(elems) => Expr::SetEnum(
            elems.iter().map(|e| substitute_expr(e, subs)).collect(),
        ),
        Expr::SetRange(l, r) => Expr::SetRange(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::SetFilter(var, domain, pred) => {
            let filtered_subs: Vec<_> = subs.iter()
                .filter(|(p, _)| p != var)
                .cloned()
                .collect();
            Expr::SetFilter(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(pred, &filtered_subs)),
            )
        }
        Expr::SetMap(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter()
                .filter(|(p, _)| p != var)
                .cloned()
                .collect();
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
            let filtered_subs: Vec<_> = subs.iter()
                .filter(|(p, _)| p != var)
                .cloned()
                .collect();
            Expr::Exists(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::Forall(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter()
                .filter(|(p, _)| p != var)
                .cloned()
                .collect();
            Expr::Forall(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::Choose(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter()
                .filter(|(p, _)| p != var)
                .cloned()
                .collect();
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
            let filtered_subs: Vec<_> = subs.iter()
                .filter(|(p, _)| p != var)
                .cloned()
                .collect();
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
            let filtered_subs: Vec<_> = subs.iter()
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
            let new_updates: Vec<_> = updates.iter()
                .map(|(keys, val)| {
                    let new_keys: Vec<_> = keys.iter()
                        .map(|k| substitute_expr(k, subs))
                        .collect();
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
            fields.iter()
                .map(|(name, val)| (name.clone(), substitute_expr(val, subs)))
                .collect(),
        ),
        Expr::RecordSet(fields) => Expr::RecordSet(
            fields.iter()
                .map(|(name, val)| (name.clone(), substitute_expr(val, subs)))
                .collect(),
        ),
        Expr::RecordAccess(rec, field) => Expr::RecordAccess(
            Box::new(substitute_expr(rec, subs)),
            field.clone(),
        ),

        Expr::TupleLit(elems) => Expr::TupleLit(
            elems.iter().map(|e| substitute_expr(e, subs)).collect(),
        ),
        Expr::TupleAccess(tup, idx) => Expr::TupleAccess(
            Box::new(substitute_expr(tup, subs)),
            *idx,
        ),

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
            let filtered_subs: Vec<_> = subs.iter()
                .filter(|(p, _)| p != var)
                .cloned()
                .collect();
            Expr::Let(
                var.clone(),
                Box::new(substitute_expr(binding, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::Case(branches) => Expr::Case(
            branches.iter()
                .map(|(cond, result)| (substitute_expr(cond, subs), substitute_expr(result, subs)))
                .collect(),
        ),

        Expr::Unchanged(vars) => Expr::Unchanged(vars.clone()),
        Expr::Prime(var) => Expr::Prime(var.clone()),

        Expr::Always(e) => Expr::Always(Box::new(substitute_expr(e, subs))),
        Expr::Eventually(e) => Expr::Eventually(Box::new(substitute_expr(e, subs))),
        Expr::LeadsTo(l, r) => Expr::LeadsTo(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::WeakFairness(var, action) => Expr::WeakFairness(
            var.clone(),
            Box::new(substitute_expr(action, subs)),
        ),
        Expr::StrongFairness(var, action) => Expr::StrongFairness(
            var.clone(),
            Box::new(substitute_expr(action, subs)),
        ),
        Expr::BoxAction(action, var) => Expr::BoxAction(
            Box::new(substitute_expr(action, subs)),
            var.clone(),
        ),
        Expr::DiamondAction(action, var) => Expr::DiamondAction(
            Box::new(substitute_expr(action, subs)),
            var.clone(),
        ),
        Expr::EnabledOp(e) => Expr::EnabledOp(Box::new(substitute_expr(e, subs))),

        Expr::QualifiedCall(inst, op, args) => Expr::QualifiedCall(
            inst.clone(),
            op.clone(),
            args.iter().map(|a| substitute_expr(a, subs)).collect(),
        ),

        Expr::LabeledAction(label, action) => Expr::LabeledAction(
            label.clone(),
            Box::new(substitute_expr(action, subs)),
        ),

        Expr::Lit(_) | Expr::OldValue | Expr::Print(_, _) | Expr::PrintT(_) |
        Expr::Assert(_, _) | Expr::JavaTime | Expr::SystemTime |
        Expr::Permutations(_) | Expr::SortSeq(_, _) | Expr::TLCToString(_) |
        Expr::RandomElement(_) | Expr::TLCGet(_) | Expr::TLCSet(_, _) |
        Expr::Any | Expr::TLCEval(_) | Expr::IsABag(_) | Expr::BagToSet(_) |
        Expr::SetToBag(_) | Expr::BagIn(_, _) | Expr::EmptyBag |
        Expr::BagAdd(_, _) | Expr::BagSub(_, _) | Expr::BagUnion(_) |
        Expr::SqSubseteq(_, _) | Expr::SubBag(_) | Expr::BagOfAll(_, _) |
        Expr::BagCardinality(_) | Expr::CopiesIn(_, _) => expr.clone(),
    }
}

pub fn resolve_instances(
    spec: &Spec,
    registry: &ModuleRegistry,
) -> Result<BTreeMap<Arc<str>, Definitions>, ModuleError> {
    let mut resolved = BTreeMap::new();

    for inst in &spec.instances {
        let alias = match &inst.alias {
            Some(a) => a.clone(),
            None => inst.module_name.clone(),
        };

        if let Some(module) = registry.get(&inst.module_name) {
            let substituted = apply_substitutions(&module.definitions, &inst.substitutions);
            resolved.insert(alias, substituted);
        }
    }

    Ok(resolved)
}
