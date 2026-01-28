use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{State, Value};

pub struct SymmetryConfig {
    symmetric_sets: Vec<BTreeSet<Value>>,
}

impl SymmetryConfig {
    pub fn new() -> Self {
        Self {
            symmetric_sets: Vec::new(),
        }
    }

    pub fn add_symmetric_set(&mut self, elements: BTreeSet<Value>) {
        if elements.len() > 1 {
            self.symmetric_sets.push(elements);
        }
    }

    pub fn is_empty(&self) -> bool {
        self.symmetric_sets.is_empty()
    }

    pub fn canonicalize<'a>(&self, state: &'a State) -> Cow<'a, State> {
        if self.symmetric_sets.is_empty() {
            return Cow::Borrowed(state);
        }

        let mut result = state.clone();
        for sym_set in &self.symmetric_sets {
            result = self.canonicalize_for_set(&result, sym_set);
        }
        Cow::Owned(result)
    }

    fn canonicalize_for_set(&self, state: &State, sym_set: &BTreeSet<Value>) -> State {
        let ordering = self.compute_element_ordering(state, sym_set);
        let canonical_elements: Vec<_> = sym_set.iter().cloned().collect();

        let mut mapping = BTreeMap::new();
        for (i, original) in ordering.iter().enumerate() {
            if i < canonical_elements.len() {
                mapping.insert(original.clone(), canonical_elements[i].clone());
            }
        }

        self.apply_mapping(state, &mapping)
    }

    fn compute_element_ordering(&self, state: &State, sym_set: &BTreeSet<Value>) -> Vec<Value> {
        let mut seen = BTreeSet::new();
        let mut ordering = Vec::new();

        for value in &state.values {
            self.collect_elements_in_order(value, sym_set, &mut seen, &mut ordering);
        }

        for elem in sym_set {
            if !seen.contains(elem) {
                ordering.push(elem.clone());
            }
        }

        ordering
    }

    fn collect_elements_in_order(
        &self,
        value: &Value,
        sym_set: &BTreeSet<Value>,
        seen: &mut BTreeSet<Value>,
        ordering: &mut Vec<Value>,
    ) {
        if sym_set.contains(value) && !seen.contains(value) {
            seen.insert(value.clone());
            ordering.push(value.clone());
            return;
        }

        match value {
            Value::Set(s) => {
                for elem in s {
                    self.collect_elements_in_order(elem, sym_set, seen, ordering);
                }
            }
            Value::Fn(f) => {
                let mut entries: Vec<_> = f.iter().collect();
                entries.sort_by(|a, b| b.1.cmp(a.1).then_with(|| a.0.cmp(b.0)));
                for (k, v) in entries {
                    self.collect_elements_in_order(v, sym_set, seen, ordering);
                    self.collect_elements_in_order(k, sym_set, seen, ordering);
                }
            }
            Value::Record(r) => {
                for v in r.values() {
                    self.collect_elements_in_order(v, sym_set, seen, ordering);
                }
            }
            Value::Tuple(t) => {
                for elem in t {
                    self.collect_elements_in_order(elem, sym_set, seen, ordering);
                }
            }
            Value::Bool(_) | Value::Int(_) | Value::Str(_) => {}
        }
    }

    fn apply_mapping(&self, state: &State, mapping: &BTreeMap<Value, Value>) -> State {
        let values = state.values.iter()
            .map(|value| self.apply_mapping_to_value(value, mapping))
            .collect();
        State { values }
    }

    fn apply_mapping_to_value(&self, value: &Value, mapping: &BTreeMap<Value, Value>) -> Value {
        if let Some(mapped) = mapping.get(value) {
            return mapped.clone();
        }

        match value {
            Value::Bool(_) | Value::Int(_) | Value::Str(_) => value.clone(),
            Value::Set(s) => {
                let mapped: BTreeSet<_> = s
                    .iter()
                    .map(|e| self.apply_mapping_to_value(e, mapping))
                    .collect();
                Value::Set(mapped)
            }
            Value::Fn(f) => {
                let mapped: BTreeMap<_, _> = f
                    .iter()
                    .map(|(k, v)| {
                        (
                            self.apply_mapping_to_value(k, mapping),
                            self.apply_mapping_to_value(v, mapping),
                        )
                    })
                    .collect();
                Value::Fn(mapped)
            }
            Value::Record(r) => {
                let mapped: BTreeMap<_, _> = r
                    .iter()
                    .map(|(k, v)| (k.clone(), self.apply_mapping_to_value(v, mapping)))
                    .collect();
                Value::Record(mapped)
            }
            Value::Tuple(t) => {
                let mapped: Vec<_> = t
                    .iter()
                    .map(|e| self.apply_mapping_to_value(e, mapping))
                    .collect();
                Value::Tuple(mapped)
            }
        }
    }
}

impl Default for SymmetryConfig {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    fn str_val(s: &str) -> Value {
        Value::Str(Arc::from(s))
    }

    #[test]
    fn empty_symmetry_returns_same_state() {
        let config = SymmetryConfig::new();
        let state = State { values: vec![Value::Int(42)] };

        let canonical = config.canonicalize(&state);
        assert_eq!(*canonical, state);
    }

    #[test]
    fn single_element_set_no_change() {
        let mut config = SymmetryConfig::new();
        config.add_symmetric_set(BTreeSet::from([str_val("a")]));

        let state = State { values: vec![str_val("a")] };

        let canonical = config.canonicalize(&state);
        assert_eq!(*canonical, state);
    }

    #[test]
    fn canonicalize_swaps_elements_based_on_first_occurrence() {
        let mut config = SymmetryConfig::new();
        config.add_symmetric_set(BTreeSet::from([str_val("p1"), str_val("p2"), str_val("p3")]));

        let mut votes = BTreeMap::new();
        votes.insert(str_val("p2"), Value::Int(1));
        votes.insert(str_val("p1"), Value::Int(0));
        votes.insert(str_val("p3"), Value::Int(0));
        let state = State { values: vec![Value::Fn(votes)] };

        let canonical = config.canonicalize(&state);

        if let Some(Value::Fn(cvotes)) = canonical.values.first() {
            assert_eq!(cvotes.get(&str_val("p1")), Some(&Value::Int(1)));
            assert_eq!(cvotes.get(&str_val("p2")), Some(&Value::Int(0)));
            assert_eq!(cvotes.get(&str_val("p3")), Some(&Value::Int(0)));
        } else {
            panic!("expected Fn value");
        }
    }

    #[test]
    fn canonicalize_produces_identical_states_for_symmetric_inputs() {
        let mut config = SymmetryConfig::new();
        config.add_symmetric_set(BTreeSet::from([str_val("a"), str_val("b")]));

        let state1 = State { values: vec![str_val("a")] };
        let state2 = State { values: vec![str_val("b")] };

        let c1 = config.canonicalize(&state1);
        let c2 = config.canonicalize(&state2);

        assert_eq!(c1, c2);
    }

    #[test]
    fn canonicalize_handles_nested_structures() {
        let mut config = SymmetryConfig::new();
        config.add_symmetric_set(BTreeSet::from([str_val("x"), str_val("y")]));

        let inner_set = BTreeSet::from([str_val("y")]);
        let state = State { values: vec![Value::Set(inner_set)] };

        let canonical = config.canonicalize(&state);

        if let Some(Value::Set(s)) = canonical.values.first() {
            assert!(s.contains(&str_val("x")));
            assert!(!s.contains(&str_val("y")));
        } else {
            panic!("expected Set value");
        }
    }
}
