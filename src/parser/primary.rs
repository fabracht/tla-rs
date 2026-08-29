use std::sync::Arc;

use crate::ast::{Expr, InstanceDecl, Value};
use crate::lexer::Token;

use super::error::{ParseError, Result};
use super::lexing::Parser;

#[derive(Debug, Clone)]
pub(super) enum Binder {
    Name(Arc<str>),
    Tuple(Vec<Binder>),
}

pub(super) fn extract_binder(expr: &Expr) -> Option<Binder> {
    match expr {
        Expr::Var(name) => Some(Binder::Name(name.clone())),
        Expr::TupleLit(elems) => {
            let mut parts = Vec::with_capacity(elems.len());
            for e in elems {
                parts.push(extract_binder(e)?);
            }
            Some(Binder::Tuple(parts))
        }
        _ => None,
    }
}

pub(super) fn wrap_binder(
    parser: &mut Parser,
    binder: Binder,
    body: Expr,
) -> Result<(Arc<str>, Expr)> {
    let mut seen: Vec<Arc<str>> = Vec::new();
    check_binder_unique(&binder, &mut seen)?;
    match binder {
        Binder::Name(name) => Ok((name, body)),
        Binder::Tuple(parts) => {
            let tup_name = parser.fresh_tuple_name();
            let wrapped = wrap_tuple_lets(parser, &tup_name, parts, body);
            Ok((tup_name, wrapped))
        }
    }
}

fn check_binder_unique(binder: &Binder, seen: &mut Vec<Arc<str>>) -> Result<()> {
    match binder {
        Binder::Name(name) => {
            if seen.iter().any(|n| n == name) {
                return Err(ParseError::new(format!(
                    "duplicate name '{}' in tuple binder",
                    name
                )));
            }
            seen.push(name.clone());
            Ok(())
        }
        Binder::Tuple(parts) => {
            for part in parts {
                check_binder_unique(part, seen)?;
            }
            Ok(())
        }
    }
}

fn wrap_tuple_lets(
    parser: &mut Parser,
    tup_name: &Arc<str>,
    parts: Vec<Binder>,
    mut body: Expr,
) -> Expr {
    for (i, part) in parts.into_iter().enumerate().rev() {
        let access = Expr::TupleAccess(Box::new(Expr::Var(tup_name.clone())), i);
        match part {
            Binder::Name(name) => {
                body = Expr::Let(name, Box::new(access), Box::new(body));
            }
            Binder::Tuple(inner) => {
                let inner_tup = parser.fresh_tuple_name();
                let inner_body = wrap_tuple_lets(parser, &inner_tup, inner, body);
                body = Expr::Let(inner_tup, Box::new(access), Box::new(inner_body));
            }
        }
    }
    body
}

impl Parser {
    pub(super) fn parse_binder(&mut self) -> Result<Binder> {
        if *self.peek() == Token::LAngle {
            self.advance();
            if *self.peek() == Token::RAngle {
                return Err(ParseError::new("empty tuple binder").with_span(self.current_span()));
            }
            let mut parts = vec![self.parse_binder()?];
            while *self.peek() == Token::Comma {
                self.advance();
                parts.push(self.parse_binder()?);
            }
            self.expect(Token::RAngle)?;
            Ok(Binder::Tuple(parts))
        } else {
            Ok(Binder::Name(self.expect_ident()?))
        }
    }
}

impl Parser {
    pub(super) fn parse_primary(&mut self) -> Result<Expr> {
        let span = self.current_span();
        match self.peek().clone() {
            Token::Int(n) => {
                self.advance();
                Ok(Expr::Lit(Value::Int(n)))
            }
            Token::Str(s) => {
                self.advance();
                Ok(Expr::Lit(Value::Str(s)))
            }
            Token::True => {
                self.advance();
                Ok(Expr::Lit(Value::Bool(true)))
            }
            Token::False => {
                self.advance();
                Ok(Expr::Lit(Value::Bool(false)))
            }
            Token::At => {
                self.advance();
                Ok(Expr::OldValue)
            }
            Token::Ident(name) if name.starts_with("WF_") => {
                let var: Arc<str> = name[3..].into();
                self.advance();
                self.expect(Token::LParen)?;
                let action = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::WeakFairness(var, Box::new(action)))
            }
            Token::Ident(name) if name.starts_with("SF_") => {
                let var: Arc<str> = name[3..].into();
                self.advance();
                self.expect(Token::LParen)?;
                let action = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::StrongFairness(var, Box::new(action)))
            }
            Token::Ident(name) => {
                self.advance();
                if *self.peek() == Token::LParen {
                    let is_recursive = self.recursive_names.contains(&name);
                    if !is_recursive
                        && !self.let_scope.contains(&name)
                        && let Some((params, body)) = self.fn_definitions.get(&name).cloned()
                    {
                        self.advance();
                        let mut args = vec![self.parse_expr()?];
                        while *self.peek() == Token::Comma {
                            self.advance();
                            args.push(self.parse_expr()?);
                        }
                        self.expect(Token::RParen)?;
                        if args.len() != params.len() {
                            return Err(format!(
                                "function {} expects {} args, got {}",
                                name,
                                params.len(),
                                args.len()
                            )
                            .into());
                        }
                        let mut result = body;
                        for (param, arg) in params.iter().zip(args) {
                            result = Expr::Let(param.clone(), Box::new(arg), Box::new(result));
                        }
                        return Ok(result);
                    }
                    self.advance();
                    let mut args = Vec::new();
                    if *self.peek() != Token::RParen {
                        args.push(self.parse_expr()?);
                        while *self.peek() == Token::Comma {
                            self.advance();
                            args.push(self.parse_expr()?);
                        }
                    }
                    self.expect(Token::RParen)?;
                    Ok(Expr::FnCall(name, args))
                } else if !self.let_scope.contains(&name)
                    && let Some(def) = self.definitions.get(&name)
                {
                    Ok(def.clone())
                } else {
                    Ok(Expr::Var(name))
                }
            }
            Token::LParen => {
                self.advance();
                self.paren_depth += 1;
                let expr = self.parse_expr()?;
                self.paren_depth -= 1;
                self.expect(Token::RParen)?;
                Ok(expr)
            }
            Token::LBrace => {
                self.advance();
                self.parse_set_or_fn()
            }
            Token::LBracket => {
                self.advance();
                self.parse_record_or_fn()
            }
            Token::LAngle => {
                self.advance();
                self.parse_tuple()
            }
            Token::And => {
                let list_col = self.current_column();
                let list_line = self.current_line();
                self.advance();
                let label = self.consume_label();
                let first = self.parse_and_item(list_col)?;
                let first = super::expr::wrap_with_label(first, label);
                let mut result = first;
                while *self.peek() == Token::And && !self.col_mismatch(list_col, list_line) {
                    self.advance();
                    let label = self.consume_label();
                    let next = self.parse_and_item(list_col)?;
                    let next = super::expr::wrap_with_label(next, label);
                    result = Expr::And(Box::new(result), Box::new(next));
                }
                Ok(result)
            }
            Token::Or => {
                let list_col = self.current_column();
                let list_line = self.current_line();
                self.advance();
                let label = self.consume_label();
                let first = self.parse_and_item(list_col)?;
                let first = super::expr::wrap_with_label(first, label);
                let mut result = first;
                while *self.peek() == Token::Or && !self.col_mismatch(list_col, list_line) {
                    self.advance();
                    let label = self.consume_label();
                    let next = self.parse_and_item(list_col)?;
                    let next = super::expr::wrap_with_label(next, label);
                    result = Expr::Or(Box::new(result), Box::new(next));
                }
                Ok(result)
            }
            other => Err(ParseError::new(format!("unexpected {other}"))
                .with_span(span)
                .with_context("expression", format!("{other}"))),
        }
    }

    pub(super) fn parse_set_or_fn(&mut self) -> Result<Expr> {
        if *self.peek() == Token::RBrace {
            self.advance();
            return Ok(Expr::SetEnum(vec![]));
        }

        let first = self.parse_expr()?;

        match self.peek() {
            Token::DotDot => {
                self.advance();
                let last = self.parse_expr()?;
                self.expect(Token::RBrace)?;
                Ok(Expr::SetRange(Box::new(first), Box::new(last)))
            }
            Token::Comma => {
                let mut elems = vec![first];
                while *self.peek() == Token::Comma {
                    self.advance();
                    elems.push(self.parse_expr()?);
                }
                self.expect(Token::RBrace)?;
                Ok(Expr::SetEnum(elems))
            }
            Token::Colon => {
                self.advance();
                let after_colon = self.parse_expr()?;
                if let Expr::In(var_expr, domain) = &first
                    && let Some(binder) = extract_binder(var_expr)
                {
                    self.expect(Token::RBrace)?;
                    let domain = domain.as_ref().clone();
                    let (var, wrapped) = wrap_binder(self, binder, after_colon)?;
                    return Ok(Expr::SetFilter(var, Box::new(domain), Box::new(wrapped)));
                }
                let mut bounds = vec![after_colon];
                while *self.peek() == Token::Comma {
                    self.advance();
                    bounds.push(self.parse_expr()?);
                }
                self.expect(Token::RBrace)?;
                self.build_set_map(first, bounds)
            }
            Token::RBrace => {
                self.advance();
                Ok(Expr::SetEnum(vec![first]))
            }
            _ => {
                let span = self.current_span();
                let tok = self.peek().clone();
                Err(ParseError::new(format!("unexpected {tok} in set literal")).with_span(span))
            }
        }
    }

    /// Build a set-image comprehension `{e : x \in S, y \in T, ...}` from the
    /// mapped expression and its bounds. A single bound is one `SetMap`; each
    /// enclosing bound maps the accumulated set and flattens it, so
    /// `{e : x \in S, y \in T}` is `UNION {{e : y \in T} : x \in S}`.
    fn build_set_map(&mut self, body: Expr, bounds: Vec<Expr>) -> Result<Expr> {
        let mut iter = bounds.into_iter().rev();
        let (var, domain) = match iter.next() {
            Some(Expr::In(var_expr, domain)) => (var_expr, domain),
            _ => return Err(self.set_map_error()),
        };
        let binder = extract_binder(&var).ok_or_else(|| self.set_map_error())?;
        let (var, wrapped) = wrap_binder(self, binder, body)?;
        let mut result = Expr::SetMap(var, domain, Box::new(wrapped));
        for bound in iter {
            let (var, domain) = match bound {
                Expr::In(var_expr, domain) => (var_expr, domain),
                _ => return Err(self.set_map_error()),
            };
            let binder = extract_binder(&var).ok_or_else(|| self.set_map_error())?;
            let (var, wrapped) = wrap_binder(self, binder, result)?;
            result = Expr::BigUnion(Box::new(Expr::SetMap(var, domain, Box::new(wrapped))));
        }
        Ok(result)
    }

    fn set_map_error(&self) -> ParseError {
        ParseError::new("expected {e : x \\in S, ...} in set comprehension")
            .with_span(self.current_span())
    }

    pub(super) fn parse_record_or_fn(&mut self) -> Result<Expr> {
        let start_pos = self.pos;

        if *self.peek() == Token::RBracket {
            self.advance();
            return Ok(Expr::SetEnum(vec![]));
        }

        let first = self.parse_expr()?;

        if *self.peek() == Token::RightArrow {
            self.advance();
            let codomain = self.parse_expr()?;
            self.expect(Token::RBracket)?;
            return Ok(Expr::FunctionSet(Box::new(first), Box::new(codomain)));
        } else if *self.peek() == Token::Except {
            self.advance();
            let updates = self.parse_except_updates()?;
            self.expect(Token::RBracket)?;
            return Ok(Expr::Except(Box::new(first), updates));
        } else if matches!(self.peek(), Token::MapsTo | Token::Colon | Token::In) {
            if *self.peek() == Token::MapsTo
                && let Expr::In(lhs, domain) = &first
                && let Some(binder) = extract_binder(lhs)
                && matches!(binder, Binder::Tuple(_))
            {
                let domain = domain.as_ref().clone();
                self.advance();
                let body = self.parse_expr()?;
                self.expect(Token::RBracket)?;
                let (var, wrapped) = wrap_binder(self, binder, body)?;
                return Ok(Expr::FnDef(var, Box::new(domain), Box::new(wrapped)));
            }
            self.pos = start_pos;
        } else if *self.peek() == Token::RBracket {
            self.advance();
            return Ok(first);
        } else {
            self.expect(Token::RBracket)?;
            return Ok(first);
        }

        if let Token::Ident(_) = self.peek() {
            let name = self.expect_ident()?;

            if *self.peek() == Token::MapsTo {
                self.advance();
                let val = self.parse_expr()?;
                let mut fields = vec![(name, val)];
                while *self.peek() == Token::Comma {
                    self.advance();
                    let field_name = self.expect_ident()?;
                    self.expect(Token::MapsTo)?;
                    let field_val = self.parse_expr()?;
                    fields.push((field_name, field_val));
                }
                self.expect(Token::RBracket)?;
                return Ok(Expr::RecordLit(fields));
            } else if *self.peek() == Token::Colon {
                self.advance();
                let domain = self.parse_expr()?;
                let mut fields = vec![(name, domain)];
                while *self.peek() == Token::Comma {
                    self.advance();
                    let field_name = self.expect_ident()?;
                    self.expect(Token::Colon)?;
                    let field_domain = self.parse_expr()?;
                    fields.push((field_name, field_domain));
                }
                self.expect(Token::RBracket)?;
                return Ok(Expr::RecordSet(fields));
            } else if *self.peek() == Token::In {
                self.advance();
                let domain = self.parse_expr()?;
                self.expect(Token::MapsTo)?;
                let body = self.parse_expr()?;
                self.expect(Token::RBracket)?;
                return Ok(Expr::FnDef(name, Box::new(domain), Box::new(body)));
            } else {
                self.pos = start_pos;
            }
        }

        let expr = self.parse_expr()?;
        if *self.peek() == Token::Except {
            self.advance();
            let updates = self.parse_except_updates()?;
            self.expect(Token::RBracket)?;
            Ok(Expr::Except(Box::new(expr), updates))
        } else {
            self.expect(Token::RBracket)?;
            Ok(Expr::FnApp(
                Box::new(Expr::Var("_fn".into())),
                Box::new(expr),
            ))
        }
    }

    pub(super) fn parse_tuple(&mut self) -> Result<Expr> {
        if *self.peek() == Token::RAngle {
            self.advance();
            if *self.peek() == Token::Underscore {
                self.advance();
                let var = self.expect_ident()?;
                return Ok(Expr::DiamondAction(Box::new(Expr::TupleLit(vec![])), var));
            }
            return Ok(Expr::TupleLit(vec![]));
        }

        let first = self.parse_expr()?;
        if *self.peek() == Token::RAngle {
            self.advance();
            if *self.peek() == Token::Underscore {
                self.advance();
                let var = self.expect_ident()?;
                return Ok(Expr::DiamondAction(Box::new(first), var));
            }
            return Ok(Expr::TupleLit(vec![first]));
        }

        let mut elems = vec![first];
        while *self.peek() == Token::Comma {
            self.advance();
            elems.push(self.parse_expr()?);
        }
        self.expect(Token::RAngle)?;
        if *self.peek() == Token::Underscore {
            self.advance();
            let var = self.expect_ident()?;
            return Ok(Expr::DiamondAction(Box::new(Expr::TupleLit(elems)), var));
        }
        Ok(Expr::TupleLit(elems))
    }

    pub(super) fn parse_unchanged(&mut self) -> Result<Expr> {
        if *self.peek() == Token::LAngle {
            self.advance();
            let mut vars = Vec::new();
            if *self.peek() != Token::RAngle {
                vars.push(self.expect_ident()?);
                while *self.peek() == Token::Comma {
                    self.advance();
                    vars.push(self.expect_ident()?);
                }
            }
            self.expect(Token::RAngle)?;
            Ok(Expr::Unchanged(vars))
        } else {
            let var = self.expect_ident()?;
            Ok(Expr::Unchanged(vec![var]))
        }
    }

    pub(super) fn parse_choose(&mut self) -> Result<Expr> {
        let binder = self.parse_binder()?;
        if *self.peek() == Token::In {
            self.advance();
            let domain = self.parse_range()?;
            self.expect(Token::Colon)?;
            let body = self.parse_expr()?;
            let (var, wrapped) = wrap_binder(self, binder, body)?;
            Ok(Expr::Choose(var, Box::new(domain), Box::new(wrapped)))
        } else if *self.peek() == Token::Colon {
            self.advance();
            let body = self.parse_expr()?;
            let (var, wrapped) = wrap_binder(self, binder, body)?;
            Ok(Expr::ChooseUnbounded(var, Box::new(wrapped)))
        } else {
            Err(
                ParseError::new(format!("unexpected {} after CHOOSE variable", self.peek()))
                    .with_span(self.current_span())
                    .with_context("`\\in` or `:`", format!("{}", self.peek())),
            )
        }
    }

    pub(super) fn parse_lambda(&mut self) -> Result<Expr> {
        let mut params = vec![self.expect_ident()?];
        while *self.peek() == Token::Comma {
            self.advance();
            params.push(self.expect_ident()?);
        }
        self.expect(Token::Colon)?;
        let body = self.parse_expr()?;
        Ok(Expr::Lambda(params, Box::new(body)))
    }

    pub(super) fn parse_quantifier(&mut self, exists: bool) -> Result<Expr> {
        let mut bindings: Vec<(Binder, Expr)> = vec![];

        loop {
            let mut binders = vec![self.parse_binder()?];
            while *self.peek() == Token::Comma {
                self.advance();
                let next = self.parse_binder()?;
                binders.push(next);
                if *self.peek() == Token::In {
                    break;
                }
            }
            self.expect(Token::In)?;
            let domain = self.parse_range()?;
            for b in binders {
                bindings.push((b, domain.clone()));
            }

            if *self.peek() == Token::Comma {
                self.advance();
            } else {
                break;
            }
        }

        self.expect(Token::Colon)?;
        let body = self.parse_quantifier_body()?;

        let mut result = body;
        for (binder, domain) in bindings.into_iter().rev() {
            let (var, wrapped) = wrap_binder(self, binder, result)?;
            if exists {
                result = Expr::Exists(var, Box::new(domain), Box::new(wrapped));
            } else {
                result = Expr::Forall(var, Box::new(domain), Box::new(wrapped));
            }
        }
        Ok(result)
    }

    pub(super) fn parse_if(&mut self) -> Result<Expr> {
        let cond = if *self.peek() == Token::And {
            self.advance();
            let mut left = self.parse_comparison()?;
            while *self.peek() == Token::And {
                self.advance();
                let right = self.parse_comparison()?;
                left = Expr::And(Box::new(left), Box::new(right));
            }
            left
        } else {
            self.parse_expr()?
        };
        self.expect(Token::Then)?;
        let then_br = self.parse_single_expr()?;
        self.expect(Token::Else)?;
        let else_br = self.parse_single_expr()?;
        Ok(Expr::If(
            Box::new(cond),
            Box::new(then_br),
            Box::new(else_br),
        ))
    }

    pub(super) fn parse_case(&mut self) -> Result<Expr> {
        let mut branches = Vec::new();
        loop {
            if *self.peek() == Token::Other {
                self.advance();
                self.expect_case_arrow()?;
                let result = self.parse_expr()?;
                branches.push((Expr::Lit(Value::Bool(true)), result));
                break;
            }
            let cond = self.parse_expr()?;
            self.expect_case_arrow()?;
            let result = self.parse_expr()?;
            branches.push((cond, result));
            if *self.peek() == Token::Always {
                self.advance();
            } else if *self.peek() == Token::LBracket {
                self.advance();
                self.expect(Token::RBracket)?;
            } else {
                break;
            }
        }
        Ok(Expr::Case(branches))
    }

    pub(super) fn expect_case_arrow(&mut self) -> Result<()> {
        let span = self.current_span();
        match self.peek() {
            Token::RightArrow | Token::MapsTo => {
                self.advance();
                Ok(())
            }
            t => Err(ParseError::new(format!("unexpected {t} in CASE branch"))
                .with_span(span)
                .with_context("`->` or `|->`", format!("{t}"))),
        }
    }

    pub(super) fn parse_let(&mut self) -> Result<Expr> {
        let mut bindings = Vec::new();
        let scope_start = self.let_scope.len();

        loop {
            if *self.peek() == Token::Recursive {
                self.advance();
                self.parse_recursive_declaration()?;
                continue;
            }

            let var = self.expect_ident()?;

            if *self.peek() == Token::LBracket {
                self.advance();
                let param = self.expect_ident()?;
                self.expect(Token::In)?;
                let domain = self.parse_range()?;
                self.expect(Token::RBracket)?;
                self.expect(Token::EqEq)?;
                let body = self.parse_expr()?;
                let fn_def = Expr::FnDef(param, Box::new(domain), Box::new(body));
                self.let_scope.push(var.clone());
                bindings.push((var, fn_def));
            } else if *self.peek() == Token::LParen {
                self.advance();
                let mut params = vec![self.expect_ident()?];
                while *self.peek() == Token::Comma {
                    self.advance();
                    params.push(self.expect_ident()?);
                }
                self.expect(Token::RParen)?;
                self.expect(Token::EqEq)?;
                let body = self.parse_expr()?;
                let fn_val = Expr::TupleLit(params.into_iter().map(Expr::Var).collect());
                self.let_scope.push(var.clone());
                bindings.push((
                    var,
                    Expr::Let("_params".into(), Box::new(fn_val), Box::new(body)),
                ));
            } else {
                self.expect(Token::EqEq)?;
                let binding = self.parse_expr()?;
                self.let_scope.push(var.clone());
                bindings.push((var, binding));
            }

            if *self.peek() == Token::Def {
                break;
            }

            if let Token::Ident(_) = self.peek()
                && self.pos + 1 < self.tokens.len()
                && matches!(
                    self.tokens[self.pos + 1].value,
                    Token::EqEq | Token::LBracket | Token::LParen
                )
            {
                continue;
            }

            break;
        }

        self.expect(Token::Def)?;
        let body_result = self.parse_expr();
        self.let_scope.truncate(scope_start);
        let mut body = body_result?;

        for (var, binding) in bindings.into_iter().rev() {
            body = Expr::Let(var, Box::new(binding), Box::new(body));
        }

        Ok(body)
    }

    pub(super) fn parse_recursive_declaration(&mut self) -> Result<()> {
        loop {
            let name = self.expect_ident()?;
            self.recursive_names.insert(name);
            if *self.peek() == Token::LParen {
                self.advance();
                while *self.peek() != Token::RParen && *self.peek() != Token::Eof {
                    self.advance();
                }
                if *self.peek() == Token::RParen {
                    self.advance();
                }
            }
            if *self.peek() != Token::Comma {
                break;
            }
            self.advance();
        }
        Ok(())
    }

    pub(super) fn parse_instance(
        &mut self,
        alias: Option<Arc<str>>,
        params: Vec<Arc<str>>,
    ) -> Result<InstanceDecl> {
        let module_name = self.expect_ident()?;
        let mut substitutions = Vec::new();
        if *self.peek() == Token::With {
            self.advance();
            loop {
                let param = self.expect_ident()?;
                self.expect(Token::LeftArrow)?;
                let expr = self.parse_expr()?;
                substitutions.push((param, expr));
                if *self.peek() != Token::Comma {
                    break;
                }
                self.advance();
            }
        }
        Ok(InstanceDecl {
            alias,
            params,
            module_name,
            substitutions,
        })
    }

    pub(super) fn parse_except_updates(&mut self) -> Result<Vec<(Vec<Expr>, Expr)>> {
        let mut updates = vec![self.parse_single_except_update()?];
        while *self.peek() == Token::Comma {
            self.advance();
            updates.push(self.parse_single_except_update()?);
        }
        Ok(updates)
    }

    pub(super) fn parse_single_except_update(&mut self) -> Result<(Vec<Expr>, Expr)> {
        self.expect(Token::Bang)?;
        let mut keys = Vec::new();
        loop {
            if *self.peek() == Token::Dot {
                self.advance();
                let field = self.expect_ident()?;
                keys.push(Expr::Lit(Value::Str(field)));
            } else if *self.peek() == Token::LBracket {
                self.advance();
                keys.push(self.parse_expr()?);
                self.expect(Token::RBracket)?;
            } else {
                break;
            }
        }
        if keys.is_empty() {
            return Err(
                ParseError::new(format!("unexpected {} in EXCEPT update", self.peek()))
                    .with_span(self.current_span())
                    .with_context("`.` or `[`", format!("{}", self.peek())),
            );
        }
        self.expect(Token::Eq)?;
        let val = self.parse_expr()?;
        Ok((keys, val))
    }
}
