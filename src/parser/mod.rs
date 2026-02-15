mod error;
mod expr;
pub(crate) mod lexing;
mod primary;
mod spec;

pub use self::error::ParseError;
pub use self::lexing::Parser;

use crate::ast::{Expr, Spec};

pub(crate) type Result<T> = std::result::Result<T, ParseError>;

pub fn parse(input: &str) -> Result<Spec> {
    let mut parser = Parser::new(input)?;
    parser.parse_spec()
}

pub fn parse_expr(input: &str) -> Result<Expr> {
    let mut parser = Parser::new(input)?;
    parser.parse_expr()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_simple_expr() {
        let expr = parse_expr("x + 1").unwrap();
        assert!(matches!(expr, Expr::Add(_, _)));
    }

    #[test]
    fn parse_primed_var() {
        let expr = parse_expr("x' = x + 1").unwrap();
        assert!(matches!(expr, Expr::Eq(_, _)));
    }

    #[test]
    fn parse_set_range() {
        let expr = parse_expr("1..5").unwrap();
        assert!(matches!(expr, Expr::SetRange(_, _)));
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
