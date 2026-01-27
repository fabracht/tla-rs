use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::ast::{Expr, FairnessConstraint, InstanceDecl, Spec, Value};
use crate::lexer::{LexError, Lexer, Token};
use crate::span::{Span, Spanned};

pub struct Parser {
    tokens: Vec<Spanned<Token>>,
    pos: usize,
    definitions: BTreeMap<Arc<str>, Expr>,
    fn_definitions: BTreeMap<Arc<str>, (Vec<Arc<str>>, Expr)>,
    recursive_names: BTreeSet<Arc<str>>,
    constants: Vec<Arc<str>>,
    extends: Vec<Arc<str>>,
    assumes: Vec<Expr>,
    instances: Vec<InstanceDecl>,
    fairness: Vec<FairnessConstraint>,
    liveness_properties: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub span: Option<Span>,
    pub expected: Option<String>,
    pub found: Option<String>,
}

impl ParseError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            span: None,
            expected: None,
            found: None,
        }
    }

    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    pub fn with_context(mut self, expected: impl Into<String>, found: impl Into<String>) -> Self {
        self.expected = Some(expected.into());
        self.found = Some(found.into());
        self
    }
}

impl From<String> for ParseError {
    fn from(s: String) -> Self {
        Self::new(s)
    }
}

impl From<&str> for ParseError {
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

impl From<LexError> for ParseError {
    fn from(e: LexError) -> Self {
        let span = e.span();
        Self::new(e.message).with_span(span)
    }
}

type Result<T> = std::result::Result<T, ParseError>;

impl Parser {
    pub fn new(input: &str) -> Result<Self> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize_spanned()?;
        Ok(Self {
            tokens,
            pos: 0,
            definitions: BTreeMap::new(),
            fn_definitions: BTreeMap::new(),
            recursive_names: BTreeSet::new(),
            constants: Vec::new(),
            extends: Vec::new(),
            assumes: Vec::new(),
            instances: Vec::new(),
            fairness: Vec::new(),
            liveness_properties: Vec::new(),
        })
    }

    fn peek(&self) -> &Token {
        self.tokens
            .get(self.pos)
            .map(|t| &t.value)
            .unwrap_or(&Token::Eof)
    }

    fn peek_n(&self, n: usize) -> &Token {
        self.tokens
            .get(self.pos + n)
            .map(|t| &t.value)
            .unwrap_or(&Token::Eof)
    }

    fn current_span(&self) -> Span {
        self.tokens
            .get(self.pos)
            .map(|t| t.span)
            .unwrap_or(Span::empty())
    }

    fn prev_span(&self) -> Span {
        if self.pos > 0 {
            self.tokens
                .get(self.pos - 1)
                .map(|t| t.span)
                .unwrap_or(Span::empty())
        } else {
            Span::empty()
        }
    }

    fn is_module_prefix(s: &str) -> bool {
        !s.is_empty()
            && (s.chars().all(|c| c.is_ascii_uppercase())
                || s.ends_with('_'))
    }

    fn is_invariant_name(name: &str) -> bool {
        for suffix in ["TypeOK", "Inv"] {
            if name.starts_with(suffix) {
                return true;
            }
            if let Some(prefix) = name.strip_suffix(suffix)
                && Self::is_module_prefix(prefix)
            {
                return true;
            }
        }
        name.starts_with("NotSolved")
    }

    fn advance(&mut self) -> Token {
        let tok = self.peek().clone();
        if tok != Token::Eof {
            self.pos += 1;
        }
        tok
    }

    fn expect(&mut self, expected: Token) -> Result<()> {
        let span = self.current_span();
        let tok = self.advance();
        if tok == expected {
            Ok(())
        } else {
            Err(ParseError::new(format!("expected {:?}, found {:?}", expected, tok))
                .with_span(span)
                .with_context(format!("{:?}", expected), format!("{:?}", tok)))
        }
    }

    fn expect_ident(&mut self) -> Result<Arc<str>> {
        let span = self.current_span();
        match self.advance() {
            Token::Ident(s) => Ok(s),
            other => Err(ParseError::new(format!("expected identifier, found {:?}", other))
                .with_span(span)
                .with_context("identifier", format!("{:?}", other))),
        }
    }

    fn skip_to_next_definition(&mut self) {
        loop {
            match self.peek() {
                Token::Eof => break,
                Token::Variables
                | Token::Constants
                | Token::Module
                | Token::Extends
                | Token::Theorem => break,
                Token::Invariant => break,
                Token::Ident(_) => {
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
                }
                _ => {
                    self.advance();
                }
            }
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
                            eprintln!("  Warning: failed to parse operator '{}': {}", name, e.message);
                            if let Some(span) = e.span {
                                eprintln!("    at offset {}..{}", span.start, span.end);
                            }
                            self.skip_to_next_definition();
                            continue;
                        }
                    };

                    let is_init_name = name.as_ref() == "Init"
                        || (name.ends_with("Init") && Self::is_module_prefix(&name[..name.len() - 4]));
                    let is_next_name = name.as_ref() == "Next"
                        || (name.ends_with("Next") && Self::is_module_prefix(&name[..name.len() - 4]));

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
                    return Err(ParseError::new(format!("unexpected token: {:?}", tok))
                        .with_span(span));
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
                self.liveness_properties.push(Expr::LeadsTo(p.clone(), q.clone()));
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
            other => Err(ParseError::new(format!("expected identifier or `_`, found {:?}", other))
                .with_span(span)
                .with_context("identifier or `_`", format!("{:?}", other))),
        }
    }

    pub fn parse_expr(&mut self) -> Result<Expr> {
        self.parse_implies()
    }

    fn parse_implies(&mut self) -> Result<Expr> {
        let mut left = self.parse_or()?;
        loop {
            match self.peek() {
                Token::Implies => {
                    self.advance();
                    let right = self.parse_or()?;
                    left = Expr::Implies(Box::new(left), Box::new(right));
                }
                Token::Equiv => {
                    self.advance();
                    let right = self.parse_or()?;
                    left = Expr::Equiv(Box::new(left), Box::new(right));
                }
                Token::LeadsTo => {
                    self.advance();
                    let right = self.parse_or()?;
                    left = Expr::LeadsTo(Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }
        Ok(left)
    }

    fn consume_label(&mut self) -> Option<Arc<str>> {
        if let Token::Ident(name) = self.peek().clone()
            && *self.peek_n(1) == Token::LabelSep
        {
            self.advance();
            self.advance();
            return Some(name);
        }
        None
    }

    fn wrap_with_label(expr: Expr, label: Option<Arc<str>>) -> Expr {
        match label {
            Some(name) => Expr::LabeledAction(name, Box::new(expr)),
            None => expr,
        }
    }

    fn parse_or(&mut self) -> Result<Expr> {
        if *self.peek() == Token::Or {
            self.advance();
            self.consume_label();
        }
        let mut left = self.parse_and()?;
        while *self.peek() == Token::Or {
            self.advance();
            let label = self.consume_label();
            let right = self.parse_and()?;
            let right = Self::wrap_with_label(right, label);
            left = Expr::Or(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Expr> {
        if *self.peek() == Token::And {
            self.advance();
            self.consume_label();
        }
        let mut left = self.parse_comparison()?;
        loop {
            match self.peek() {
                Token::And => {
                    self.advance();
                    let label = self.consume_label();
                    let right = self.parse_comparison()?;
                    let right = Self::wrap_with_label(right, label);
                    left = Expr::And(Box::new(left), Box::new(right));
                }
                Token::ActionCompose => {
                    self.advance();
                    let right = self.parse_comparison()?;
                    left = Expr::ActionCompose(Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }
        Ok(left)
    }

    fn parse_single_expr(&mut self) -> Result<Expr> {
        self.parse_single_implies()
    }

    fn parse_single_implies(&mut self) -> Result<Expr> {
        let mut left = self.parse_single_or()?;
        loop {
            match self.peek() {
                Token::Implies => {
                    self.advance();
                    let right = self.parse_single_or()?;
                    left = Expr::Implies(Box::new(left), Box::new(right));
                }
                Token::Equiv => {
                    self.advance();
                    let right = self.parse_single_or()?;
                    left = Expr::Equiv(Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }
        Ok(left)
    }

    fn parse_single_or(&mut self) -> Result<Expr> {
        let mut left = self.parse_single_and()?;
        while *self.peek() == Token::Or {
            self.advance();
            let right = self.parse_single_and()?;
            left = Expr::Or(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_single_and(&mut self) -> Result<Expr> {
        let mut left = self.parse_comparison()?;
        loop {
            match self.peek() {
                Token::And => {
                    self.advance();
                    let right = self.parse_comparison()?;
                    left = Expr::And(Box::new(left), Box::new(right));
                }
                Token::ActionCompose => {
                    self.advance();
                    let right = self.parse_comparison()?;
                    left = Expr::ActionCompose(Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }
        Ok(left)
    }

    fn parse_quantifier_body(&mut self) -> Result<Expr> {
        let mut left = self.parse_quantifier_or()?;
        loop {
            match self.peek() {
                Token::Implies => {
                    self.advance();
                    let right = self.parse_quantifier_or()?;
                    left = Expr::Implies(Box::new(left), Box::new(right));
                }
                Token::Equiv => {
                    self.advance();
                    let right = self.parse_quantifier_or()?;
                    left = Expr::Equiv(Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }
        Ok(left)
    }

    fn parse_quantifier_or(&mut self) -> Result<Expr> {
        let mut left = self.parse_comparison()?;
        while *self.peek() == Token::Or {
            self.advance();
            let right = self.parse_comparison()?;
            left = Expr::Or(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_comparison(&mut self) -> Result<Expr> {
        let left = self.parse_range()?;
        match self.peek() {
            Token::Eq => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::Eq(Box::new(left), Box::new(right)))
            }
            Token::Neq => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::Neq(Box::new(left), Box::new(right)))
            }
            Token::Lt => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::Lt(Box::new(left), Box::new(right)))
            }
            Token::Le => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::Le(Box::new(left), Box::new(right)))
            }
            Token::Gt => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::Gt(Box::new(left), Box::new(right)))
            }
            Token::Ge => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::Ge(Box::new(left), Box::new(right)))
            }
            Token::In => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::In(Box::new(left), Box::new(right)))
            }
            Token::NotIn => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::NotIn(Box::new(left), Box::new(right)))
            }
            Token::Subseteq => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::Subset(Box::new(left), Box::new(right)))
            }
            Token::ProperSubset => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::ProperSubset(Box::new(left), Box::new(right)))
            }
            Token::Supseteq => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::Subset(Box::new(right), Box::new(left)))
            }
            Token::ProperSupset => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::ProperSubset(Box::new(right), Box::new(left)))
            }
            Token::SqSubseteq => {
                self.advance();
                let right = self.parse_range()?;
                Ok(Expr::SqSubseteq(Box::new(left), Box::new(right)))
            }
            _ => Ok(left),
        }
    }

    fn parse_range(&mut self) -> Result<Expr> {
        let left = self.parse_additive()?;
        if *self.peek() == Token::DotDot {
            self.advance();
            let right = self.parse_additive()?;
            Ok(Expr::SetRange(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    fn parse_additive(&mut self) -> Result<Expr> {
        let mut left = self.parse_multiplicative()?;
        loop {
            match self.peek() {
                Token::Plus => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = Expr::Add(Box::new(left), Box::new(right));
                }
                Token::Minus => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = Expr::Sub(Box::new(left), Box::new(right));
                }
                Token::Union => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = Expr::Union(Box::new(left), Box::new(right));
                }
                Token::Intersect => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = Expr::Intersect(Box::new(left), Box::new(right));
                }
                Token::SetMinus => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = Expr::SetMinus(Box::new(left), Box::new(right));
                }
                Token::Times => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = Expr::Cartesian(Box::new(left), Box::new(right));
                }
                Token::Concat => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = Expr::Concat(Box::new(left), Box::new(right));
                }
                Token::AtAt => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = Expr::FnMerge(Box::new(left), Box::new(right));
                }
                Token::ColonGt => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = Expr::SingleFn(Box::new(left), Box::new(right));
                }
                Token::CustomOp(op_name) => {
                    let op_name = op_name.clone();
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = Expr::CustomOp(op_name, Box::new(left), Box::new(right));
                }
                Token::BagAdd => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = Expr::BagAdd(Box::new(left), Box::new(right));
                }
                Token::BagSub => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = Expr::BagSub(Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }
        Ok(left)
    }

    fn parse_multiplicative(&mut self) -> Result<Expr> {
        let mut left = self.parse_exponential()?;
        loop {
            match self.peek() {
                Token::Star => {
                    self.advance();
                    let right = self.parse_exponential()?;
                    left = Expr::Mul(Box::new(left), Box::new(right));
                }
                Token::Div => {
                    self.advance();
                    let right = self.parse_exponential()?;
                    left = Expr::Div(Box::new(left), Box::new(right));
                }
                Token::Mod => {
                    self.advance();
                    let right = self.parse_exponential()?;
                    left = Expr::Mod(Box::new(left), Box::new(right));
                }
                Token::Ampersand => {
                    self.advance();
                    let right = self.parse_exponential()?;
                    left = Expr::BitwiseAnd(Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }
        Ok(left)
    }

    fn parse_exponential(&mut self) -> Result<Expr> {
        let base = self.parse_unary()?;
        if matches!(self.peek(), Token::Caret) {
            self.advance();
            let exp = self.parse_exponential()?;
            Ok(Expr::Exp(Box::new(base), Box::new(exp)))
        } else {
            Ok(base)
        }
    }

    fn parse_unary(&mut self) -> Result<Expr> {
        match self.peek() {
            Token::Not => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(Expr::Not(Box::new(expr)))
            }
            Token::Minus => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(Expr::Neg(Box::new(expr)))
            }
            Token::Domain => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(Expr::Domain(Box::new(expr)))
            }
            Token::Subset => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(Expr::Powerset(Box::new(expr)))
            }
            Token::BigUnion => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(Expr::BigUnion(Box::new(expr)))
            }
            Token::Cardinality => {
                self.advance();
                self.expect(Token::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::Cardinality(Box::new(expr)))
            }
            Token::IsFiniteSet => {
                self.advance();
                self.expect(Token::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::IsFiniteSet(Box::new(expr)))
            }
            Token::Len => {
                self.advance();
                self.expect(Token::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::Len(Box::new(expr)))
            }
            Token::Head => {
                self.advance();
                self.expect(Token::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::Head(Box::new(expr)))
            }
            Token::Tail => {
                self.advance();
                self.expect(Token::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::Tail(Box::new(expr)))
            }
            Token::Append => {
                self.advance();
                self.expect(Token::LParen)?;
                let seq = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let elem = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::Append(Box::new(seq), Box::new(elem)))
            }
            Token::SubSeq => {
                self.advance();
                self.expect(Token::LParen)?;
                let seq = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let start = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let end = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::SubSeq(Box::new(seq), Box::new(start), Box::new(end)))
            }
            Token::SelectSeq => {
                self.advance();
                self.expect(Token::LParen)?;
                let seq = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let test = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::SelectSeq(Box::new(seq), Box::new(test)))
            }
            Token::Seq => {
                self.advance();
                self.expect(Token::LParen)?;
                let domain = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::SeqSet(Box::new(domain)))
            }
            Token::Print => {
                self.advance();
                self.expect(Token::LParen)?;
                let val = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::Print(Box::new(val), Box::new(expr)))
            }
            Token::Assert => {
                self.advance();
                self.expect(Token::LParen)?;
                let cond = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let msg = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::Assert(Box::new(cond), Box::new(msg)))
            }
            Token::JavaTime => {
                self.advance();
                Ok(Expr::JavaTime)
            }
            Token::SystemTime => {
                self.advance();
                Ok(Expr::SystemTime)
            }
            Token::Permutations => {
                self.advance();
                self.expect(Token::LParen)?;
                let set = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::Permutations(Box::new(set)))
            }
            Token::SortSeq => {
                self.advance();
                self.expect(Token::LParen)?;
                let seq = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let cmp = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::SortSeq(Box::new(seq), Box::new(cmp)))
            }
            Token::PrintT => {
                self.advance();
                self.expect(Token::LParen)?;
                let val = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::PrintT(Box::new(val)))
            }
            Token::TLCToString => {
                self.advance();
                self.expect(Token::LParen)?;
                let val = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::TLCToString(Box::new(val)))
            }
            Token::RandomElement => {
                self.advance();
                self.expect(Token::LParen)?;
                let set = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::RandomElement(Box::new(set)))
            }
            Token::TLCGet => {
                self.advance();
                self.expect(Token::LParen)?;
                let idx = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::TLCGet(Box::new(idx)))
            }
            Token::TLCSet => {
                self.advance();
                self.expect(Token::LParen)?;
                let idx = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let val = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::TLCSet(Box::new(idx), Box::new(val)))
            }
            Token::Any => {
                self.advance();
                Ok(Expr::Any)
            }
            Token::TLCEval => {
                self.advance();
                self.expect(Token::LParen)?;
                let val = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::TLCEval(Box::new(val)))
            }
            Token::IsABag => {
                self.advance();
                self.expect(Token::LParen)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::IsABag(Box::new(bag)))
            }
            Token::BagToSet => {
                self.advance();
                self.expect(Token::LParen)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::BagToSet(Box::new(bag)))
            }
            Token::SetToBag => {
                self.advance();
                self.expect(Token::LParen)?;
                let set = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::SetToBag(Box::new(set)))
            }
            Token::BagIn => {
                self.advance();
                self.expect(Token::LParen)?;
                let elem = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::BagIn(Box::new(elem), Box::new(bag)))
            }
            Token::EmptyBag => {
                self.advance();
                Ok(Expr::EmptyBag)
            }
            Token::BagUnion => {
                self.advance();
                self.expect(Token::LParen)?;
                let bags = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::BagUnion(Box::new(bags)))
            }
            Token::SubBag => {
                self.advance();
                self.expect(Token::LParen)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::SubBag(Box::new(bag)))
            }
            Token::BagOfAll => {
                self.advance();
                self.expect(Token::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::BagOfAll(Box::new(expr), Box::new(bag)))
            }
            Token::BagCardinality => {
                self.advance();
                self.expect(Token::LParen)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::BagCardinality(Box::new(bag)))
            }
            Token::CopiesIn => {
                self.advance();
                self.expect(Token::LParen)?;
                let elem = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(Expr::CopiesIn(Box::new(elem), Box::new(bag)))
            }
            Token::Unchanged => {
                self.advance();
                self.parse_unchanged()
            }
            Token::Choose => {
                self.advance();
                self.parse_choose()
            }
            Token::Lambda => {
                self.advance();
                self.parse_lambda()
            }
            Token::Exists => {
                self.advance();
                self.parse_quantifier(true)
            }
            Token::Forall => {
                self.advance();
                self.parse_quantifier(false)
            }
            Token::If => {
                self.advance();
                self.parse_if()
            }
            Token::Case => {
                self.advance();
                self.parse_case()
            }
            Token::Let => {
                self.advance();
                self.parse_let()
            }
            Token::Eventually => {
                self.advance();
                let inner = self.parse_unary()?;
                Ok(Expr::Eventually(Box::new(inner)))
            }
            Token::Always => {
                self.advance();
                if *self.peek() == Token::LBracket {
                    self.advance();
                    let action = self.parse_expr()?;
                    self.expect(Token::RBracket)?;
                    self.expect(Token::Underscore)?;
                    let var = self.expect_ident()?;
                    return Ok(Expr::BoxAction(Box::new(action), var));
                }
                let inner = self.parse_unary()?;
                Ok(Expr::Always(Box::new(inner)))
            }
            Token::Enabled => {
                self.advance();
                let action = self.parse_unary()?;
                Ok(Expr::EnabledOp(Box::new(action)))
            }
            _ => self.parse_postfix(),
        }
    }

    fn parse_postfix(&mut self) -> Result<Expr> {
        let mut expr = self.parse_primary()?;
        loop {
            match self.peek() {
                Token::Prime => {
                    self.advance();
                    if let Expr::Var(name) = expr {
                        expr = Expr::Prime(name);
                    } else {
                        return Err(ParseError::new("prime can only be applied to variable")
                            .with_span(self.prev_span()));
                    }
                }
                Token::LBracket => {
                    self.advance();
                    if *self.peek() == Token::Except {
                        self.advance();
                        let updates = self.parse_except_updates()?;
                        self.expect(Token::RBracket)?;
                        expr = Expr::Except(Box::new(expr), updates);
                    } else {
                        let idx = self.parse_expr()?;
                        self.expect(Token::RBracket)?;
                        if let Expr::Lit(Value::Int(n)) = &idx {
                            if *n > 0 {
                                expr = Expr::TupleAccess(Box::new(expr), (*n - 1) as usize);
                            } else {
                                expr = Expr::FnApp(Box::new(expr), Box::new(idx));
                            }
                        } else {
                            expr = Expr::FnApp(Box::new(expr), Box::new(idx));
                        }
                    }
                }
                Token::Dot => {
                    self.advance();
                    let field = self.expect_ident()?;
                    expr = Expr::RecordAccess(Box::new(expr), field);
                }
                Token::TransitiveClosure => {
                    self.advance();
                    expr = Expr::TransitiveClosure(Box::new(expr));
                }
                Token::ReflexiveTransitiveClosure => {
                    self.advance();
                    expr = Expr::ReflexiveTransitiveClosure(Box::new(expr));
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<Expr> {
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
                if *self.peek() == Token::Bang {
                    self.advance();
                    let op_name = self.expect_ident()?;
                    let mut args = Vec::new();
                    if *self.peek() == Token::LParen {
                        self.advance();
                        if *self.peek() != Token::RParen {
                            args.push(self.parse_expr()?);
                            while *self.peek() == Token::Comma {
                                self.advance();
                                args.push(self.parse_expr()?);
                            }
                        }
                        self.expect(Token::RParen)?;
                    }
                    return Ok(Expr::QualifiedCall(name, op_name, args));
                }
                if *self.peek() == Token::LParen {
                    let is_recursive = self.recursive_names.contains(&name);
                    if !is_recursive
                        && let Some((params, body)) = self.fn_definitions.get(&name).cloned() {
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
                } else if let Some(def) = self.definitions.get(&name) {
                    Ok(def.clone())
                } else {
                    Ok(Expr::Var(name))
                }
            }
            Token::LParen => {
                self.advance();
                let expr = self.parse_expr()?;
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
                self.advance();
                let first = self.parse_comparison()?;
                let mut result = first;
                while *self.peek() == Token::And {
                    self.advance();
                    let next = self.parse_comparison()?;
                    result = Expr::And(Box::new(result), Box::new(next));
                }
                Ok(result)
            }
            Token::Or => {
                self.advance();
                let first = self.parse_comparison()?;
                let mut result = first;
                while *self.peek() == Token::Or {
                    self.advance();
                    let next = self.parse_comparison()?;
                    result = Expr::Or(Box::new(result), Box::new(next));
                }
                Ok(result)
            }
            other => Err(ParseError::new(format!("unexpected token in expression: {:?}", other))
                .with_span(span)
                .with_context("expression", format!("{:?}", other))),
        }
    }

    fn parse_set_or_fn(&mut self) -> Result<Expr> {
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
                self.expect(Token::RBrace)?;
                if let Expr::In(var_expr, domain) = &first
                    && let Expr::Var(var) = var_expr.as_ref()
                {
                    return Ok(Expr::SetFilter(var.clone(), domain.clone(), Box::new(after_colon)));
                }
                if let Expr::In(var_expr, domain) = after_colon
                    && let Expr::Var(var) = *var_expr
                {
                    return Ok(Expr::SetMap(var, domain, Box::new(first)));
                }
                Err(ParseError::new("expected {x \\in S : P} or {e : x \\in S} in set comprehension")
                    .with_span(self.current_span()))
            }
            Token::RBrace => {
                self.advance();
                Ok(Expr::SetEnum(vec![first]))
            }
            _ => {
                let span = self.current_span();
                let tok = self.peek().clone();
                Err(ParseError::new(format!("unexpected token in set: {:?}", tok))
                    .with_span(span))
            }
        }
    }

    fn parse_record_or_fn(&mut self) -> Result<Expr> {
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
        } else if matches!(
            self.peek(),
            Token::MapsTo | Token::Colon | Token::In
        ) {
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
            Ok(Expr::FnApp(Box::new(Expr::Var("_fn".into())), Box::new(expr)))
        }
    }

    fn parse_tuple(&mut self) -> Result<Expr> {
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

    fn parse_unchanged(&mut self) -> Result<Expr> {
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

    fn parse_choose(&mut self) -> Result<Expr> {
        let var = self.expect_ident()?;
        if *self.peek() == Token::In {
            self.advance();
            let domain = self.parse_additive()?;
            self.expect(Token::Colon)?;
            let body = self.parse_expr()?;
            Ok(Expr::Choose(var, Box::new(domain), Box::new(body)))
        } else if *self.peek() == Token::Colon {
            self.advance();
            let body = self.parse_expr()?;
            let empty_domain = Expr::SetEnum(vec![]);
            Ok(Expr::Choose(var, Box::new(empty_domain), Box::new(body)))
        } else {
            Err(ParseError::new("expected `\\in` or `:` after CHOOSE variable")
                .with_span(self.current_span())
                .with_context("`\\in` or `:`", format!("{:?}", self.peek())))
        }
    }

    fn parse_lambda(&mut self) -> Result<Expr> {
        let mut params = vec![self.expect_ident()?];
        while *self.peek() == Token::Comma {
            self.advance();
            params.push(self.expect_ident()?);
        }
        self.expect(Token::Colon)?;
        let body = self.parse_expr()?;
        Ok(Expr::Lambda(params, Box::new(body)))
    }

    fn parse_quantifier(&mut self, exists: bool) -> Result<Expr> {
        let mut bindings: Vec<(Arc<str>, Expr)> = vec![];

        loop {
            let mut vars = vec![self.expect_ident()?];
            while *self.peek() == Token::Comma {
                self.advance();
                let next_var = self.expect_ident()?;
                vars.push(next_var);
                if *self.peek() == Token::In {
                    break;
                }
            }
            self.expect(Token::In)?;
            let domain = self.parse_range()?;
            for v in vars {
                bindings.push((v, domain.clone()));
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
        for (var, domain) in bindings.into_iter().rev() {
            if exists {
                result = Expr::Exists(var, Box::new(domain), Box::new(result));
            } else {
                result = Expr::Forall(var, Box::new(domain), Box::new(result));
            }
        }
        Ok(result)
    }

    fn parse_if(&mut self) -> Result<Expr> {
        let cond = self.parse_single_expr()?;
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

    fn parse_case(&mut self) -> Result<Expr> {
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

    fn expect_case_arrow(&mut self) -> Result<()> {
        let span = self.current_span();
        match self.peek() {
            Token::RightArrow | Token::MapsTo => {
                self.advance();
                Ok(())
            }
            t => Err(ParseError::new(format!("expected `->` or `|->` in CASE, found {:?}", t))
                .with_span(span)
                .with_context("`->` or `|->`", format!("{:?}", t))),
        }
    }

    fn parse_let(&mut self) -> Result<Expr> {
        let mut bindings = Vec::new();

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
                let domain = self.parse_additive()?;
                self.expect(Token::RBracket)?;
                self.expect(Token::EqEq)?;
                let body = self.parse_expr()?;
                let fn_def = Expr::FnDef(param, Box::new(domain), Box::new(body));
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
                bindings.push((var, Expr::Let("_params".into(), Box::new(fn_val), Box::new(body))));
            } else {
                self.expect(Token::EqEq)?;
                let binding = self.parse_expr()?;
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
        let mut body = self.parse_expr()?;

        for (var, binding) in bindings.into_iter().rev() {
            body = Expr::Let(var, Box::new(binding), Box::new(body));
        }

        Ok(body)
    }

    fn parse_recursive_declaration(&mut self) -> Result<()> {
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

    fn parse_instance(&mut self, alias: Option<Arc<str>>) -> Result<InstanceDecl> {
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
            module_name,
            substitutions,
        })
    }

    fn parse_except_updates(&mut self) -> Result<Vec<(Vec<Expr>, Expr)>> {
        let mut updates = vec![self.parse_single_except_update()?];
        while *self.peek() == Token::Comma {
            self.advance();
            updates.push(self.parse_single_except_update()?);
        }
        Ok(updates)
    }

    fn parse_single_except_update(&mut self) -> Result<(Vec<Expr>, Expr)> {
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
            return Err(ParseError::new("expected `.` or `[` after `!` in EXCEPT")
                .with_span(self.current_span())
                .with_context("`.` or `[`", format!("{:?}", self.peek())));
        }
        self.expect(Token::Eq)?;
        let val = self.parse_expr()?;
        Ok((keys, val))
    }
}

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
        let expr = parse_expr("IF x < 5 THEN /\\ x' = x + 1 /\\ y' = y ELSE /\\ x' = x /\\ y' = y + 1").unwrap();
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
