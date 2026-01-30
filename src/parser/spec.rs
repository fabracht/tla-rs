use std::sync::Arc;

use crate::ast::{Expr, FairnessConstraint, Spec};
use crate::lexer::Token;

use super::error::{ParseError, Result};
use super::lexing::Parser;

impl Parser {
    pub fn parse_spec(&mut self) -> Result<Spec> {
        let mut vars = Vec::new();
        let mut init = None;
        let mut next = None;
        let mut invariants = Vec::new();
        let mut invariant_names = Vec::new();

        while *self.peek() != Token::Eof {
            match self.peek() {
                Token::Module => {
                    self.advance();
                    self.expect_ident()?;
                }
                Token::Extends => {
                    self.advance();
                    let modules = self.parse_var_list()?;
                    self.extends.extend(modules);
                }
                Token::Variables => {
                    self.advance();
                    vars = self.parse_var_list()?;
                }
                Token::Constants => {
                    self.advance();
                    let consts = self.parse_var_list()?;
                    self.constants.extend(consts);
                }
                Token::Assume => {
                    self.advance();
                    if let Token::Ident(_) = self.peek() {
                        let start = self.pos;
                        self.advance();
                        if *self.peek() == Token::EqEq {
                            self.advance();
                            let expr = self.parse_expr()?;
                            self.assumes.push(expr);
                            continue;
                        }
                        self.pos = start;
                    }
                    let expr = self.parse_expr()?;
                    self.assumes.push(expr);
                }
                Token::Theorem => {
                    self.advance();
                    while *self.peek() != Token::Eof
                        && !matches!(
                            self.peek(),
                            Token::Variables
                                | Token::Constants
                                | Token::Module
                                | Token::Extends
                                | Token::Theorem
                        )
                    {
                        if let Token::Ident(_) = self.peek() {
                            let start = self.pos;
                            self.advance();
                            if *self.peek() == Token::EqEq {
                                self.pos = start;
                                break;
                            }
                            if *self.peek() == Token::LParen {
                                self.advance();
                                let mut depth = 1;
                                while depth > 0 && *self.peek() != Token::Eof {
                                    match self.peek() {
                                        Token::LParen => depth += 1,
                                        Token::RParen => depth -= 1,
                                        _ => {}
                                    }
                                    self.advance();
                                }
                                if *self.peek() == Token::EqEq {
                                    self.pos = start;
                                    break;
                                }
                            }
                        } else {
                            self.advance();
                        }
                    }
                }
                Token::Recursive => {
                    self.advance();
                    self.parse_recursive_declaration()?;
                }
                Token::Local => {
                    self.advance();
                    if *self.peek() == Token::Instance {
                        self.advance();
                        let inst = self.parse_instance(None)?;
                        self.instances.push(inst);
                    } else if let Token::Ident(_) = self.peek() {
                        self.skip_to_next_definition();
                    }
                }
                Token::Instance => {
                    self.advance();
                    let inst = self.parse_instance(None)?;
                    self.instances.push(inst);
                }
                Token::Lemma | Token::ProofStep => {
                    self.skip_to_next_definition();
                }
                Token::By | Token::Qed | Token::ProofDef | Token::Enabled => {
                    self.skip_to_next_definition();
                }
                Token::Semicolon
                | Token::Dollar
                | Token::Pipe
                | Token::Caret
                | Token::Ampersand => {
                    self.advance();
                }
                Token::Ident(name) => {
                    let name = name.clone();
                    self.advance();

                    if let Token::CustomOp(_) = self.peek() {
                        self.advance();
                        if let Token::Ident(_) = self.peek() {
                            self.advance();
                        }
                        if *self.peek() == Token::EqEq {
                            self.advance();
                            self.skip_to_next_definition();
                            continue;
                        }
                    }

                    let params = if *self.peek() == Token::LParen {
                        self.advance();
                        let params = self.parse_var_list()?;
                        self.expect(Token::RParen)?;
                        Some(params)
                    } else {
                        None
                    };

                    self.expect(Token::EqEq)?;

                    if name.as_ref() == "Spec" {
                        match self.parse_expr() {
                            Ok(spec_expr) => {
                                self.extract_fairness_and_liveness(&spec_expr);
                            }
                            Err(_) => {
                                self.skip_to_next_definition();
                            }
                        }
                        continue;
                    }

                    if *self.peek() == Token::Instance {
                        self.advance();
                        let inst = self.parse_instance(Some(name))?;
                        self.instances.push(inst);
                        continue;
                    }

                    let expr = match self.parse_expr() {
                        Ok(e) => e,
                        Err(e) => {
                            eprintln!(
                                "  Warning: failed to parse operator '{}': {}",
                                name, e.message
                            );
                            if let Some(span) = e.span {
                                eprintln!("    at offset {}..{}", span.start, span.end);
                            }
                            self.skip_to_next_definition();
                            continue;
                        }
                    };

                    let is_init_name = name.as_ref() == "Init"
                        || (name.ends_with("Init")
                            && Self::is_module_prefix(&name[..name.len() - 4]));
                    let is_next_name = name.as_ref() == "Next"
                        || (name.ends_with("Next")
                            && Self::is_module_prefix(&name[..name.len() - 4]));

                    if is_init_name {
                        init = Some(expr.clone());
                        self.definitions.insert(name, expr);
                    } else if is_next_name {
                        next = Some(expr.clone());
                        self.definitions.insert(name, expr);
                    } else if Self::is_invariant_name(&name) {
                        invariants.push(expr.clone());
                        invariant_names.push(Some(name.clone()));
                        self.definitions.insert(name, expr);
                    } else if let Some(params) = params {
                        self.fn_definitions.insert(name, (params, expr));
                    } else {
                        self.definitions.insert(name, expr);
                    }
                }
                Token::Invariant => {
                    self.advance();
                    self.expect(Token::EqEq)?;
                    invariants.push(self.parse_expr()?);
                    invariant_names.push(None);
                }
                _ => {
                    let span = self.current_span();
                    let tok = self.peek().clone();
                    let mut err = ParseError::new(format!("unexpected {tok}"))
                        .with_span(span)
                        .with_context("definition or declaration", format!("{tok}"));
                    if matches!(tok, Token::And | Token::Or) {
                        err = err.with_help(
                            "conjunction/disjunction lists must have each `/\\` or `\\/` at the same column"
                        );
                    }
                    return Err(err);
                }
            }
        }

        let init = init.ok_or("missing Init")?;
        let next = next.ok_or("missing Next")?;

        let mut all_defs = self.fn_definitions.clone();
        for (name, expr) in &self.definitions {
            all_defs.insert(name.clone(), (vec![], expr.clone()));
        }

        Ok(Spec {
            vars,
            constants: self.constants.clone(),
            extends: self.extends.clone(),
            definitions: all_defs,
            assumes: self.assumes.clone(),
            instances: self.instances.clone(),
            init,
            next,
            invariants,
            invariant_names,
            fairness: self.fairness.clone(),
            liveness_properties: self.liveness_properties.clone(),
        })
    }

    fn extract_fairness_and_liveness(&mut self, expr: &Expr) {
        match expr {
            Expr::WeakFairness(var, action) => {
                self.fairness.push(FairnessConstraint::Weak(
                    Expr::Var(var.clone()),
                    (**action).clone(),
                ));
            }
            Expr::StrongFairness(var, action) => {
                self.fairness.push(FairnessConstraint::Strong(
                    Expr::Var(var.clone()),
                    (**action).clone(),
                ));
            }
            Expr::Eventually(inner) => {
                self.liveness_properties.push((**inner).clone());
            }
            Expr::LeadsTo(p, q) => {
                self.liveness_properties
                    .push(Expr::LeadsTo(p.clone(), q.clone()));
            }
            Expr::And(l, r) => {
                self.extract_fairness_and_liveness(l);
                self.extract_fairness_and_liveness(r);
            }
            Expr::Or(l, r) => {
                self.extract_fairness_and_liveness(l);
                self.extract_fairness_and_liveness(r);
            }
            Expr::Always(inner) => {
                if let Expr::Eventually(p) = inner.as_ref() {
                    self.liveness_properties.push((**p).clone());
                } else {
                    self.extract_fairness_and_liveness(inner);
                }
            }
            Expr::BoxAction(inner, _) => {
                self.extract_fairness_and_liveness(inner);
            }
            _ => {}
        }
    }

    fn parse_var_list(&mut self) -> Result<Vec<Arc<str>>> {
        let mut vars = Vec::new();
        vars.push(self.parse_param()?);
        while *self.peek() == Token::Comma {
            self.advance();
            vars.push(self.parse_param()?);
        }
        Ok(vars)
    }

    fn parse_param(&mut self) -> Result<Arc<str>> {
        let span = self.current_span();
        match self.peek() {
            Token::Ident(name) => {
                let name = name.clone();
                self.advance();
                if *self.peek() == Token::LParen {
                    self.advance();
                    while *self.peek() != Token::RParen && *self.peek() != Token::Eof {
                        self.advance();
                    }
                    if *self.peek() == Token::RParen {
                        self.advance();
                    }
                }
                Ok(name)
            }
            Token::Underscore => {
                self.advance();
                Ok("_".into())
            }
            other => Err(ParseError::new(format!("unexpected {other}"))
                .with_span(span)
                .with_context("identifier or `_`", format!("{other}"))),
        }
    }
}
