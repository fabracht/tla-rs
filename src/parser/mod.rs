mod error;
mod expr;
pub(crate) mod lexing;
mod primary;
mod spec;

pub use self::error::ParseError;
pub use self::lexing::Parser;

use crate::ast::{Expr, Spec};
use crate::span::Spanned;

pub(crate) type Result<T> = std::result::Result<T, ParseError>;

pub fn parse(input: &str) -> Result<Spec> {
    let mut parser = Parser::new(input)?;
    parser.parse_spec()
}

pub fn parse_with_warnings(input: &str) -> Result<(Spec, Vec<Spanned<String>>)> {
    let mut parser = Parser::new(input)?;
    let spec = parser.parse_spec()?;
    let warnings = parser.take_warnings();
    Ok((spec, warnings))
}

pub fn parse_expr(input: &str) -> Result<Expr> {
    let mut parser = Parser::new(input)?;
    parser.parse_expr()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn parse_simple_expr() {
        let expr = parse_expr("x + 1").unwrap();
        assert!(matches!(expr, Expr::Add(_, _)));
    }

    #[test]
    fn postfix_operators_follow_a_builtin_application() {
        let (spec, warnings) = parse_with_warnings(
            "---- MODULE M ----\nEXTENDS Sequences\nVARIABLES s, r\n\
             Primed == Len(s)'\nIndexed == Head(s)[2]\nField == Head(r).a\n====\n",
        )
        .unwrap();
        assert!(warnings.is_empty(), "{warnings:?}");
        let body = |name: &str| spec.definitions.get(name).map(|(_, b)| (**b).clone());
        assert!(
            matches!(body("Primed"), Some(Expr::Len(inner)) if matches!(*inner, Expr::Prime(_))),
            "Len(s)' is Len(s'): {:?}",
            body("Primed")
        );
        assert!(
            matches!(body("Indexed"), Some(Expr::TupleAccess(inner, 1)) if matches!(*inner, Expr::Head(_))),
            "{:?}",
            body("Indexed")
        );
        assert!(
            matches!(body("Field"), Some(Expr::RecordAccess(inner, ref field)) if matches!(*inner, Expr::Head(_)) && field.as_ref() == "a"),
            "{:?}",
            body("Field")
        );
    }

    #[test]
    fn a_box_action_outside_always_is_a_step_or_a_stutter() {
        let named = parse_expr("[x' > x]_<<x, y>>").unwrap();
        assert!(
            matches!(&named, Expr::Or(_, unchanged) if matches!(unchanged.as_ref(), Expr::Unchanged(names) if names.len() == 2)),
            "{named:?}"
        );
        let expression = parse_expr("[x' > x]_(x + y)").unwrap();
        assert!(
            matches!(&expression, Expr::Or(_, unchanged) if matches!(unchanged.as_ref(), Expr::Eq(_, _))),
            "{expression:?}"
        );
        assert!(matches!(
            parse_expr("ENABLED [x' > x]_x").unwrap(),
            Expr::EnabledOp(_)
        ));
    }

    #[test]
    fn parse_primed_var() {
        let expr = parse_expr("x' = x + 1").unwrap();
        assert!(matches!(expr, Expr::Eq(_, _)));
    }

    #[test]
    fn prime_distributes_over_defined_operator() {
        let (spec, _) =
            parse_with_warnings("---- MODULE M ----\nVARIABLES x\nNN == x >= 0\nP == NN'\n====\n")
                .unwrap();
        let body = spec.definitions.get("P").map(|(_, b)| (**b).clone());
        match body {
            Some(Expr::Ge(l, r)) => {
                assert!(
                    matches!(*l, Expr::Prime(_)),
                    "state var must be primed: {l:?}"
                );
                assert!(matches!(*r, Expr::Lit(_)));
            }
            other => panic!("expected `x' >= 0`, got {other:?}"),
        }
    }

    #[test]
    fn slash_division_warns_but_div_does_not() {
        let (_, warnings) =
            parse_with_warnings("---- MODULE M ----\nVARIABLES x\nA == (7 / 2) + (9 / 4)\n====\n")
                .unwrap();
        assert_eq!(
            warnings.len(),
            1,
            "two `/` uses must yield exactly one warning: {warnings:?}"
        );
        assert!(warnings[0].value.contains("integer division"));

        let (_, none) =
            parse_with_warnings("---- MODULE M ----\nVARIABLES x\nA == 7 \\div 2\n====\n").unwrap();
        assert!(none.is_empty(), "`\\div` must not warn: {none:?}");
    }

    #[test]
    fn parse_set_range() {
        let expr = parse_expr("1..5").unwrap();
        assert!(matches!(expr, Expr::SetRange(_, _)));
    }

    #[test]
    fn line_and_column_from_byte_offset() {
        let parser = Parser::new("ab\ncde\nf").unwrap();
        let at = |o| (parser.line_of(o), parser.column_of(o));
        assert_eq!(at(0), (0, 0));
        assert_eq!(at(1), (0, 1));
        assert_eq!(at(3), (1, 0));
        assert_eq!(at(5), (1, 2));
        assert_eq!(at(7), (2, 0));
    }

    #[test]
    fn parse_set_enum() {
        let expr = parse_expr("{1, 2, 3}").unwrap();
        if let Expr::SetEnum(elems) = expr {
            assert_eq!(elems.len(), 3);
        } else {
            panic!("expected SetEnum");
        }
    }

    #[test]
    fn parse_exists() {
        let expr = parse_expr("\\E x \\in {1, 2} : x > 0").unwrap();
        assert!(matches!(expr, Expr::Exists(_, _, _)));
    }

    #[test]
    fn parse_unchanged() {
        let expr = parse_expr("UNCHANGED <<x, y>>").unwrap();
        if let Expr::Unchanged(vars) = expr {
            assert_eq!(vars.len(), 2);
        } else {
            panic!("expected Unchanged");
        }
    }

    #[test]
    fn parse_if_then_else() {
        let expr = parse_expr("IF x > 0 THEN x ELSE 0").unwrap();
        assert!(matches!(expr, Expr::If(_, _, _)));
    }

    #[test]
    fn parse_if_with_conjunction_list() {
        let expr =
            parse_expr("IF x < 5 THEN /\\ x' = x + 1 /\\ y' = y ELSE /\\ x' = x /\\ y' = y + 1")
                .unwrap();
        if let Expr::If(_, then_br, else_br) = expr {
            assert!(matches!(*then_br, Expr::And(_, _)));
            assert!(matches!(*else_br, Expr::And(_, _)));
        } else {
            panic!("expected If");
        }
    }

    #[test]
    fn parse_if_condition_with_or() {
        let expr = parse_expr("IF x > 5 \\/ y > 5 THEN 1 ELSE 0").unwrap();
        if let Expr::If(cond, _, _) = expr {
            assert!(matches!(*cond, Expr::Or(_, _)));
        } else {
            panic!("expected If");
        }
    }

    #[test]
    fn parse_if_condition_with_and() {
        let expr = parse_expr("IF x > 0 /\\ y > 0 THEN 1 ELSE 0").unwrap();
        if let Expr::If(cond, _, _) = expr {
            assert!(matches!(*cond, Expr::And(_, _)));
        } else {
            panic!("expected If");
        }
    }

    #[test]
    fn parse_fn_def() {
        let expr = parse_expr("[x \\in {1, 2} |-> x + 1]").unwrap();
        assert!(matches!(expr, Expr::FnDef(_, _, _)));
    }

    #[test]
    fn parse_record() {
        let expr = parse_expr("[a |-> 1, b |-> 2]").unwrap();
        if let Expr::RecordLit(fields) = expr {
            assert_eq!(fields.len(), 2);
        } else {
            panic!("expected RecordLit");
        }
    }

    #[test]
    fn parse_tuple() {
        let expr = parse_expr("<<1, 2, 3>>").unwrap();
        if let Expr::TupleLit(elems) = expr {
            assert_eq!(elems.len(), 3);
        } else {
            panic!("expected TupleLit");
        }
    }

    #[test]
    fn parse_inline_and_within_conjunction_list() {
        let input = "/\\ a \\in S /\\ b > 0\n/\\ c \\in T /\\ d > 1";
        let expr = parse_expr(input).unwrap();
        if let Expr::And(left, right) = expr {
            assert!(matches!(*left, Expr::And(_, _)));
            assert!(matches!(*right, Expr::And(_, _)));
        } else {
            panic!("expected top-level And");
        }
    }

    #[test]
    fn parse_simple_infix_and() {
        let expr = parse_expr("a /\\ b /\\ c").unwrap();
        assert!(matches!(expr, Expr::And(_, _)));
    }

    #[test]
    fn exists_in_conjunction_list_does_not_absorb_outer_conjuncts() {
        let input = "\
/\\ \\E x \\in {1, 2}:
      /\\ x > 0
/\\ y' = y + 1
/\\ z' = z";
        let expr = parse_expr(input).unwrap();
        fn count_and_nodes(e: &Expr) -> usize {
            match e {
                Expr::And(l, r) => 1 + count_and_nodes(l) + count_and_nodes(r),
                _ => 0,
            }
        }
        let top_and_count = count_and_nodes(&expr);
        assert_eq!(
            top_and_count, 2,
            "outer conjunction list should have 3 items (2 And nodes)"
        );
        if let Expr::And(left, _) = &expr {
            if let Expr::And(inner_left, _) = left.as_ref() {
                assert!(
                    matches!(inner_left.as_ref(), Expr::Exists(_, _, _)),
                    "first conjunct should be Exists, got {:?}",
                    inner_left
                );
            } else {
                panic!("expected nested And, got {:?}", left);
            }
        } else {
            panic!("expected top-level And");
        }
    }

    fn disjuncts(e: &Expr) -> usize {
        match e {
            Expr::Or(l, r) => disjuncts(l) + disjuncts(r),
            _ => 1,
        }
    }

    #[test]
    fn disjunct_right_of_the_bullet_continues_the_quantifier_body() {
        let input = r"\/ \E i \in {1, 2} : x' = i \/ x' = -i
      \/ x' = 9
\/ x' = 0";
        let expr = parse_expr(input).unwrap();
        let Expr::Or(first, _) = &expr else {
            panic!("expected a two-item list, got {expr:?}");
        };
        let Expr::Exists(_, _, body) = first.as_ref() else {
            panic!("expected the first item to be the quantifier, got {first:?}");
        };
        assert_eq!(disjuncts(body), 3, "the continued line is part of the body");
        assert_eq!(disjuncts(&expr), 2);
    }

    #[test]
    fn disjunct_right_of_a_conjunct_bullet_continues_the_quantifier_body() {
        let input = r"/\ x # 100
/\ \E i \in {1, 2} : x' = i
     \/ x' = -i";
        let expr = parse_expr(input).unwrap();
        let Expr::And(_, second) = &expr else {
            panic!("expected a two-item list, got {expr:?}");
        };
        let Expr::Exists(_, _, body) = second.as_ref() else {
            panic!("expected the second conjunct to be the quantifier, got {second:?}");
        };
        assert_eq!(
            disjuncts(body),
            2,
            "the bound `i` is in scope on the next line"
        );
    }

    #[test]
    fn disjunct_right_of_the_bullet_continues_the_else_branch() {
        let input = r"\/ IF x > 3 THEN x' = 1 ELSE x' = 2 \/ x' = 3
      \/ x' = 4
\/ x' = 0";
        let expr = parse_expr(input).unwrap();
        let Expr::Or(first, _) = &expr else {
            panic!("expected a two-item list, got {expr:?}");
        };
        let Expr::If(_, _, else_branch) = first.as_ref() else {
            panic!("expected the first item to be IF, got {first:?}");
        };
        assert_eq!(disjuncts(else_branch), 3);
    }

    fn conjuncts(e: &Expr) -> usize {
        match e {
            Expr::And(l, r) => conjuncts(l) + conjuncts(r),
            _ => 1,
        }
    }

    #[test]
    fn an_inlined_call_does_not_capture_a_call_site_name() {
        let spec = parse(
            "Pair(a, b) == <<a, b>>\nApply(F(_), v) == F(v)\n\
             P == \\E b \\in {7} : Pair(b, 1)\nQ == \\E v \\in {5} : Apply(LAMBDA a : a < v, 3)",
        )
        .unwrap();
        let mentions = |name: &str, needle: &str| {
            format!("{:?}", spec.definitions.get(name).unwrap().1).contains(needle)
        };
        assert!(
            mentions("P", "b$0"),
            "the parameter b is renamed away from the argument b"
        );
        assert!(
            mentions("Q", "v$0"),
            "the parameter v is renamed away from the LAMBDA's v"
        );
    }

    #[test]
    fn implication_binds_looser_than_junctions_and_equivalence() {
        assert!(matches!(
            parse_expr(r"TRUE \/ TRUE => FALSE").unwrap(),
            Expr::Implies(l, _) if matches!(*l, Expr::Or(_, _))
        ));
        assert!(matches!(
            parse_expr(r"/\ FALSE => TRUE /\ FALSE").unwrap(),
            Expr::Implies(_, r) if matches!(*r, Expr::And(_, _))
        ));
        assert!(matches!(
            parse_expr("FALSE => TRUE <=> FALSE").unwrap(),
            Expr::Implies(_, r) if matches!(*r, Expr::Equiv(_, _))
        ));
        assert!(matches!(
            parse_expr("TRUE <=> TRUE => FALSE").unwrap(),
            Expr::Implies(l, _) if matches!(*l, Expr::Equiv(_, _))
        ));
    }

    #[test]
    fn leads_to_in_an_item_stays_in_the_item() {
        let input = r"/\ A
/\ P ~> Q";
        let Expr::And(_, item) = parse_expr(input).unwrap() else {
            panic!("expected a two-item list");
        };
        assert!(matches!(item.as_ref(), Expr::LeadsTo(_, _)));
    }

    #[test]
    fn implication_at_the_bullet_takes_the_whole_list() {
        let input = r"/\ x > 10
/\ x < 20
=> x = 42";
        let Expr::Implies(list, _) = parse_expr(input).unwrap() else {
            panic!("expected the list to be the antecedent");
        };
        assert_eq!(conjuncts(&list), 2);
        let input = r"\/ x > 10
\/ x < 0
<=> x = 42";
        assert!(
            matches!(parse_expr(input).unwrap(), Expr::Equiv(list, _) if disjuncts(&list) == 2)
        );
    }

    #[test]
    fn implication_right_of_the_bullet_continues_the_item() {
        let input = r"/\ x > 1
/\ x < 0
     => x = 42";
        let expr = parse_expr(input).unwrap();
        let Expr::And(_, last) = &expr else {
            panic!("expected a two-item list, got {expr:?}");
        };
        assert!(matches!(last.as_ref(), Expr::Implies(_, _)));
    }

    #[test]
    fn implication_at_an_inner_bullet_takes_the_inner_list() {
        let inner = r"/\ x < 5
/\ \/ x < 5
   \/ x > 10
   => x = 42";
        let Expr::And(_, item) = parse_expr(inner).unwrap() else {
            panic!("expected a two-item outer list");
        };
        assert!(matches!(item.as_ref(), Expr::Implies(list, _) if disjuncts(list) == 2));
        let outer = r"/\ x < 5
/\ \/ x < 5
   \/ x > 10
=> x = 42";
        let Expr::Implies(list, _) = parse_expr(outer).unwrap() else {
            panic!("expected the outer list to be the antecedent");
        };
        assert_eq!(conjuncts(&list), 2);
    }

    #[test]
    fn implication_at_the_bullet_ends_a_quantifier_body_in_an_item() {
        let input = r"\A i \in S :
  /\ i > 10
  /\ x < 20
  => x = 42";
        let Expr::Forall(_, _, body) = parse_expr(input).unwrap() else {
            panic!("expected a quantifier");
        };
        assert!(matches!(body.as_ref(), Expr::Implies(list, _) if conjuncts(list) == 2));
        let input = r"/\ x > 5
/\ \A i \in S : i > 0
=> x = 42";
        assert!(
            matches!(parse_expr(input).unwrap(), Expr::Implies(list, _) if conjuncts(&list) == 2)
        );
    }

    #[test]
    fn disjunct_right_of_the_bullet_continues_the_item() {
        let input = r"\/ x' = 1 \/ x' = 2
      \/ x' = 3
\/ x' = 4";
        assert_eq!(disjuncts(&parse_expr(input).unwrap()), 4);
    }

    #[test]
    fn parse_inline_disjunctions_in_bulleted_list() {
        let input = r#"
            VARIABLES x

            Init == x = 0

            A == x' = 1
            B == x' = 2
            C == x' = 3
            D == x' = 4
            E == x' = 5

            Next ==
                \/ A \/ B \/ C
                \/ D
                \/ E
        "#;
        let spec = parse(input).unwrap();
        assert!(spec.next.is_some());
    }

    #[test]
    fn variables_declared_over_several_statements_are_all_declared() {
        let spec =
            parse("VARIABLES x\nVARIABLE y\nCONSTANT N\nCONSTANTS M\nInit == x = y").unwrap();
        assert_eq!(spec.vars, [Arc::from("x"), Arc::from("y")]);
        assert_eq!(spec.constants, [Arc::from("N"), Arc::from("M")]);
    }

    #[test]
    fn a_name_declared_again_with_the_same_kind_is_declared_once_with_a_warning() {
        let (spec, warnings) =
            parse_with_warnings("VARIABLES x\nVARIABLE x, y\nCONSTANT N, N\nInit == x = y")
                .unwrap();
        assert_eq!(spec.vars, [Arc::from("x"), Arc::from("y")]);
        assert_eq!(spec.constants, [Arc::from("N")]);
        assert_eq!(warnings.len(), 2, "{warnings:?}");
    }

    #[test]
    fn a_name_declared_as_both_constant_and_variable_is_an_error() {
        let Err(error) = parse("CONSTANT x\nVARIABLE x\nInit == x = 0") else {
            panic!("a name declared as a constant and a variable should not parse");
        };
        assert!(error.message.contains("both"), "{}", error.message);
    }

    fn unparsed(input: &str, name: &str) -> (Spec, crate::ast::UnparsedDefinition) {
        let (spec, warnings) = parse_with_warnings(input).expect("the module parses");
        let unparsed = spec
            .unparsed_definition(name)
            .cloned()
            .unwrap_or_else(|| panic!("`{name}` should be recorded as unparsed: {warnings:?}"));
        assert!(
            warnings.iter().any(|w| w.value.contains("failed to parse")),
            "{warnings:?}"
        );
        (spec, unparsed)
    }

    #[test]
    fn a_definition_whose_body_does_not_parse_stays_defined_with_its_parse_error() {
        let (spec, bad) = unparsed("VARIABLE x\nBad == [a |-> ]\nInit == x = 0", "Bad");
        assert_eq!((bad.line, bad.column), (2, 15));
        assert!(bad.message.contains("unexpected `]`"), "{}", bad.message);
        assert!(spec.init.is_some(), "the next definition still parses");
    }

    #[test]
    fn a_parameterized_definition_that_does_not_parse_keeps_its_parameters() {
        let (spec, _) = unparsed("VARIABLE x\nBad(a, b) == [a |-> ]\nInit == x = 0", "Bad");
        let (params, _) = spec.definitions.get("Bad").expect("Bad stays defined");
        assert_eq!(params, &[Arc::from("a"), Arc::from("b")]);
    }

    #[test]
    fn an_init_that_does_not_parse_is_the_init_and_fails_when_used() {
        let (spec, _) = unparsed("VARIABLE x\nInit == x = [a |-> ]\nNext == x' = x", "Init");
        assert!(
            matches!(spec.init, Some(Expr::Unparsed(_))),
            "{:?}",
            spec.init
        );
    }

    #[test]
    fn a_proof_assume_is_not_a_module_assume() {
        let spec = parse(
            "VARIABLE x\nInit == x = 0\nTHEOREM Lem == ASSUME NEW S, NEW y \\in S PROVE y \\in S\n  <1>1. ASSUME NEW z PROVE z = z\n    OBVIOUS\n  <1>2. QED BY <1>1\nASSUME TRUE\nNext == x' = x",
        )
        .expect("the proofs are skipped");
        assert_eq!(spec.assumes.len(), 1);
        assert!(spec.init.is_some() && spec.next.is_some());
    }

    #[test]
    fn definitions_indented_right_of_a_failed_one_are_kept() {
        let (spec, _) = unparsed(
            "VARIABLE x\n  Bad == [i \\in 1..2, j \\in 1..2 |-> i]\n    Init == x = 0\n    Next == x' = 1 - x",
            "Bad",
        );
        assert!(matches!(spec.init, Some(Expr::Eq(_, _))), "{:?}", spec.init);
        assert!(spec.next.is_some());
    }

    #[test]
    fn a_failed_instance_definition_does_not_become_an_unnamed_instance() {
        let (spec, _) = unparsed(
            "VARIABLE x\nM == INSTANCE Foo WITH p <- [a |-> ]\nInit == x = 0",
            "M",
        );
        assert!(spec.instances.is_empty(), "{:?}", spec.instances);
        let (spec, _) = unparsed("VARIABLE x\nM(a,) == INSTANCE Foo\nInit == x = 0", "M");
        assert!(spec.instances.is_empty(), "{:?}", spec.instances);
        assert!(spec.init.is_some());
    }

    #[test]
    fn an_invariant_that_does_not_parse_is_still_an_invariant() {
        let (spec, _) = unparsed("VARIABLE x\nInvBad == x = ]\nInit == x = 0", "InvBad");
        assert_eq!(spec.invariant_names, vec![Some(Arc::from("InvBad"))]);
        assert!(matches!(spec.invariants.as_slice(), [Expr::Unparsed(_)]));
    }

    #[test]
    fn a_spec_that_does_not_parse_is_a_liveness_obligation() {
        let (spec, _) = unparsed("VARIABLE x\nSpec == Init /\\ ]\nInit == x = 0", "Spec");
        assert!(
            matches!(
                spec.liveness_properties.as_slice(),
                [property] if matches!(property.formula, Expr::Unparsed(_))
            ),
            "{:?}",
            spec.liveness_properties
        );
    }

    #[test]
    fn a_malformed_parameter_list_keeps_its_names_and_is_not_the_init() {
        let (spec, _) = unparsed("VARIABLE x\nInit(a b) == x = ]\nNext == x' = x", "Init");
        assert!(spec.init.is_none());
        let (params, _) = spec
            .definitions
            .get("Init")
            .expect("Init(a b) stays defined");
        assert_eq!(params, &[Arc::from("a"), Arc::from("b")]);
    }

    #[test]
    fn a_stray_separator_after_a_body_does_not_fail_the_definition() {
        let spec = parse("VARIABLE x\nInit == x = 0\nNext == x' = 1 - x ;\nInv == x \\in {0, 1}")
            .expect("the spec parses");
        assert!(matches!(spec.next, Some(Expr::Eq(_, _))), "{:?}", spec.next);
    }

    #[test]
    fn an_infix_definition_whose_body_does_not_parse_is_recorded_under_its_symbol() {
        let (_, bad) = unparsed("VARIABLE x\na \\o b == ]\nInit == x = 0", "o");
        assert_eq!(bad.line, 2);
    }

    #[test]
    fn a_spec_definition_whose_body_does_not_parse_is_recorded() {
        let (spec, _) = unparsed(
            "VARIABLE x\nInit == x = 0\nSpec == Init /\\ )\nNext == x' = x",
            "Spec",
        );
        assert!(spec.next.is_some());
    }

    #[test]
    fn a_body_that_stops_before_the_next_definition_is_recorded() {
        let (spec, bad) = unparsed("VARIABLE x\nBad == x $$ 1\nInit == x = 0", "Bad");
        assert_eq!((bad.line, bad.column), (2, 10));
        assert!(spec.init.is_some());
    }

    #[test]
    fn a_function_definition_is_recorded_as_unparsed() {
        let (spec, f) = unparsed("VARIABLE x\nf[n \\in 1..3] == n\nInit == x = f[1]", "f");
        assert_eq!((f.line, f.column), (2, 2));
        assert!(spec.init.is_some());
    }

    #[test]
    fn the_column_counts_characters() {
        let (_, bad) = unparsed("VARIABLE x\nBad == \"é\" = [a |-> ]\nInit == x = 0", "Bad");
        assert_eq!((bad.line, bad.column), (2, 21));
    }

    #[test]
    fn a_let_definition_in_a_failed_body_does_not_replace_a_top_level_one() {
        let (spec, _) = unparsed(
            "VARIABLE x\nb == 100\nBad == LET a == ]\n           b == 2\n           c == 3\n       IN a + b\nInit == x = b",
            "Bad",
        );
        let (_, b) = spec.definitions.get("b").expect("b stays defined");
        assert!(
            matches!(b.as_ref(), Expr::Lit(crate::ast::Value::Int(100))),
            "{b:?}"
        );
        assert!(!spec.definitions.contains_key("c"));
        assert!(spec.init.is_some());
    }

    #[test]
    fn an_empty_body_does_not_take_the_next_definition_with_it() {
        let (spec, bad) = unparsed("VARIABLE x\nBad ==\nInit == x = 0\nNext == x' = x", "Bad");
        assert_eq!(bad.line, 3);
        assert!(spec.init.is_some() && spec.next.is_some());
    }

    #[test]
    fn a_parameterized_spec_named_operator_keeps_its_parameters() {
        let spec = parse("VARIABLE x\nMySpec(a) == a + 1\nInit == x = MySpec(1)").unwrap();
        let (params, _) = spec.definitions.get("MySpec").expect("MySpec is defined");
        assert_eq!(params, &[Arc::from("a")]);
    }

    #[test]
    fn a_theorem_does_not_swallow_the_unit_after_it() {
        let spec =
            parse("VARIABLE x\nTHEOREM x = x\nASSUME TRUE\nINSTANCE Naturals\nInit == x = 0")
                .unwrap();
        assert_eq!(spec.assumes.len(), 1);
        assert_eq!(spec.instances.len(), 1);
    }

    #[test]
    fn a_separator_mentioning_module_does_not_open_one() {
        let spec = parse("---- MODULE M ----\nVARIABLE x\n---- helpers used by MODULE M ----\nInit == x = 0\n====\nnot TLA+\n")
            .expect("text after ==== is ignored");
        assert!(spec.init.is_some());
    }

    #[test]
    fn a_top_level_name_without_a_definition_header_is_an_error() {
        let Err(error) = parse("VARIABLE x\nthis is not a definition\nInit == x = 0") else {
            panic!("text that is not a definition must not parse");
        };
        assert!(error.message.contains("unexpected"), "{}", error.message);
    }

    #[test]
    fn text_after_the_end_of_the_module_is_ignored() {
        let spec = parse("---- MODULE M ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\n====\nnot TLA+ at all\n")
            .expect("text after ==== is not part of the module");
        assert!(spec.next.is_some());
        assert!(
            spec.definitions
                .values()
                .all(|(_, body)| !matches!(body.as_ref(), Expr::Unparsed(_)))
        );
    }

    #[test]
    fn a_nested_module_does_not_end_the_enclosing_one() {
        let spec = parse("---- MODULE Outer ----\nVARIABLE x\n---- MODULE Inner ----\nA == 1\n====\nInit == x = 0\n====\ntrailing\n")
            .expect("the outer module continues after the inner one");
        assert!(spec.init.is_some());
    }

    #[test]
    fn parse_spec_definition_stored() {
        let input = r#"
            VARIABLES x

            Init == x = 0

            Next == x' = x + 1

            vars == <<x>>

            Spec == Init /\ [][Next]_vars
        "#;
        let spec = parse(input).unwrap();
        assert!(
            spec.definitions.contains_key("Spec"),
            "Spec definition should be stored in definitions"
        );
    }

    #[test]
    fn negation_binds_looser_than_in() {
        let expr = parse_expr("~state \\in {\"bar\", \"baz\"}").unwrap();
        if let Expr::Not(inner) = expr {
            assert!(
                matches!(*inner, Expr::In(_, _)),
                "~state \\in S should parse as ~(state \\in S), got {:?}",
                inner
            );
        } else {
            panic!("expected Not at top level");
        }
    }

    #[test]
    fn negation_binds_looser_than_eq() {
        let expr = parse_expr("~x = y").unwrap();
        if let Expr::Not(inner) = expr {
            assert!(
                matches!(*inner, Expr::Eq(_, _)),
                "~x = y should parse as ~(x = y), got {:?}",
                inner
            );
        } else {
            panic!("expected Not at top level");
        }
    }

    #[test]
    fn parse_spec_counter() {
        let input = r#"
            VARIABLES count

            Init == count = 0

            Next == count' = count + 1 /\ count < 3

            Inv == count <= 3
        "#;
        let spec = parse(input).unwrap();
        assert_eq!(spec.vars.len(), 1);
        assert_eq!(spec.vars[0].as_ref(), "count");
        assert_eq!(spec.invariants.len(), 1);
    }
}
