use std::sync::Arc;

use crate::ast::{Expr, LivenessProperty, Spec};
use crate::lexer::Token;

use super::error::{ParseError, Result};
use super::lexing::Parser;

impl Parser {
    fn infix_op_name(tok: &Token) -> Option<Arc<str>> {
        match tok {
            Token::CustomOp(n) => Some(n.clone()),
            Token::BagAdd => Some(Arc::from("oplus")),
            Token::BagSub => Some(Arc::from("ominus")),
            Token::Concat => Some(Arc::from("o")),
            _ => None,
        }
    }

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
                    let declared = self.parse_declared_names(&vars, true)?;
                    vars.extend(declared);
                }
                Token::Constants => {
                    self.advance();
                    let declared = self.parse_declared_names(&vars, false)?;
                    self.constants.extend(declared);
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
                        let inst = self.parse_instance(None, Vec::new())?;
                        self.instances.push(inst);
                    } else if let Token::Ident(_) = self.peek() {
                        self.skip_to_next_definition();
                    }
                }
                Token::Instance => {
                    self.advance();
                    let inst = self.parse_instance(None, Vec::new())?;
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

                    if let Some(sym) = Self::infix_op_name(self.peek())
                        && matches!(self.peek_n(1), Token::Ident(_))
                        && *self.peek_n(2) == Token::EqEq
                    {
                        self.advance();
                        let rhs = self.expect_ident()?;
                        self.expect(Token::EqEq)?;
                        match self.parse_expr() {
                            Ok(body) => {
                                self.user_infix_ops.insert(sym.clone());
                                self.fn_definitions.insert(sym, (vec![name, rhs], body));
                            }
                            Err(e) => {
                                let message = format!(
                                    "failed to parse infix operator '\\{}': {}",
                                    sym, e.message
                                );
                                let span = e.span.unwrap_or_default();
                                self.warnings.push(crate::span::Spanned::new(message, span));
                                self.skip_to_next_definition();
                            }
                        }
                        continue;
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

                    if name.as_ref() == "Spec" || name.ends_with("Spec") {
                        match self.parse_expr() {
                            Ok(spec_expr) => {
                                self.extract_fairness_and_liveness(&name, &spec_expr);
                                self.definitions.insert(name, spec_expr);
                            }
                            Err(_) => {
                                self.skip_to_next_definition();
                            }
                        }
                        continue;
                    }

                    if *self.peek() == Token::Instance {
                        self.advance();
                        let inst = self.parse_instance(Some(name), params.unwrap_or_default())?;
                        self.instances.push(inst);
                        continue;
                    }

                    let expr = match self.parse_expr() {
                        Ok(e) => e,
                        Err(e) => {
                            let message =
                                format!("failed to parse operator '{}': {}", name, e.message);
                            let span = e.span.unwrap_or_default();
                            self.warnings.push(crate::span::Spanned::new(message, span));
                            self.skip_to_next_definition();
                            continue;
                        }
                    };

                    let is_zero_arg = params.is_none();
                    let is_init_name = is_zero_arg
                        && (name.as_ref() == "Init"
                            || (name.ends_with("Init")
                                && Self::is_module_prefix(&name[..name.len() - 4])));
                    let is_next_name = is_zero_arg
                        && (name.as_ref() == "Next"
                            || (name.ends_with("Next")
                                && Self::is_module_prefix(&name[..name.len() - 4])));

                    if is_init_name {
                        init = Some(expr.clone());
                        self.definitions.insert(name, expr);
                    } else if is_next_name {
                        next = Some(expr.clone());
                        self.definitions.insert(name, expr);
                    } else if is_zero_arg && Self::is_invariant_name(&name) {
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

        let mut all_defs: crate::eval::Definitions = self
            .fn_definitions
            .iter()
            .map(|(name, (params, body))| (name.clone(), (params.clone(), Arc::new(body.clone()))))
            .collect();
        for (name, expr) in &self.definitions {
            all_defs.insert(name.clone(), (vec![], std::sync::Arc::new(expr.clone())));
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
            quantified_fairness: self.quantified_fairness.clone(),
            liveness_properties: self.liveness_properties.clone(),
            safety_properties: Vec::new(),
            temporal_assumptions: Vec::new(),
            constant_substitutions: Vec::new(),
        })
    }

    fn extract_fairness_and_liveness(&mut self, name: &Arc<str>, expr: &Expr) {
        let mut liveness = Vec::new();
        let mut warnings = Vec::new();
        crate::ast::collect_temporal(
            expr,
            &mut self.fairness,
            &mut liveness,
            &mut self.quantified_fairness,
            &mut warnings,
        );
        self.liveness_properties
            .extend(liveness.into_iter().map(|formula| LivenessProperty {
                name: name.clone(),
                formula,
                from_specification: true,
            }));
        for warning in warnings {
            self.warnings.push(crate::span::Spanned::new(
                warning,
                crate::span::Span::default(),
            ));
        }
    }

    /// The names a `VARIABLES` (`variables` true) or `CONSTANTS` declaration adds.
    /// A module may declare its variables and constants over several statements. As
    /// in SANY, declaring a name again with the same kind is a warning and the name is
    /// declared once, while a name that is both a variable and a constant is an error.
    fn parse_declared_names(
        &mut self,
        vars: &[Arc<str>],
        variables: bool,
    ) -> Result<Vec<Arc<str>>> {
        let mut names: Vec<Arc<str>> = Vec::new();
        loop {
            let span = self.current_span();
            let name = self.parse_param()?;
            let (same_kind, other_kind) = if variables {
                (vars.contains(&name), self.constants.contains(&name))
            } else {
                (self.constants.contains(&name), vars.contains(&name))
            };
            if other_kind {
                return Err(ParseError::new(format!(
                    "`{name}` is declared both as a CONSTANT and as a VARIABLE"
                ))
                .with_span(span));
            }
            if same_kind || names.contains(&name) {
                self.warnings.push(crate::span::Spanned::new(
                    format!("multiple declarations of `{name}`; it is declared once"),
                    span,
                ));
            } else {
                names.push(name);
            }
            if *self.peek() != Token::Comma {
                return Ok(names);
            }
            self.advance();
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
