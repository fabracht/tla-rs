use std::collections::BTreeSet;
use std::sync::Arc;

use tla_checker::ast::Env;
use tla_checker::checker::{CheckResult, CheckerConfig, check};
use tla_checker::parser::parse;

/// `\E p \in Procs : StepA(p) \/ StepB(p)` must attribute transitions to the
/// branch that fired, not to the enclosing `Next` definition.
const QUANTIFIED_DISJUNCTION: &str = r#"---- MODULE labels ----
VARIABLES pc
Procs == {1, 2}
Init == pc = [p \in Procs |-> "A"]
StepA(p) == pc[p] = "A" /\ pc' = [pc EXCEPT ![p] = "B"]
StepB(p) == pc[p] = "B" /\ pc' = [pc EXCEPT ![p] = "A"]
Next == \E p \in Procs : StepA(p) \/ StepB(p)
===="#;

fn labels(source: &str, use_inference_engine: bool) -> BTreeSet<String> {
    let spec = parse(source).expect("spec parses");
    let config = CheckerConfig {
        use_inference_engine,
        quiet: true,
        ..CheckerConfig::default()
    };
    let result = check(&spec, &Env::new(), &config);
    let CheckResult::Ok(stats) = result else {
        panic!("expected a clean check, got {result:?}");
    };
    stats
        .transitions_by_action
        .keys()
        .filter_map(|name| name.as_ref().map(Arc::to_string))
        .collect()
}

#[test]
fn quantified_disjunction_keeps_branch_labels_under_walker() {
    assert_eq!(
        labels(QUANTIFIED_DISJUNCTION, false),
        BTreeSet::from(["StepA".to_string(), "StepB".to_string()])
    );
}

#[test]
fn quantified_disjunction_keeps_branch_labels_under_inference() {
    assert_eq!(
        labels(QUANTIFIED_DISJUNCTION, true),
        BTreeSet::from(["StepA".to_string(), "StepB".to_string()])
    );
}

#[test]
fn top_level_disjunction_labels_are_unchanged() {
    let source = QUANTIFIED_DISJUNCTION.replace(
        "Next == \\E p \\in Procs : StepA(p) \\/ StepB(p)",
        "Next == (\\E p \\in Procs : StepA(p)) \\/ (\\E p \\in Procs : StepB(p))",
    );
    assert_eq!(
        labels(&source, false),
        BTreeSet::from(["StepA".to_string(), "StepB".to_string()])
    );
}
