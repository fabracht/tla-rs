use std::sync::Arc;

use crate::ast::{Expr, Value};
use crate::lexer::Token;

use super::error::Result;
use super::lexing::Parser;

impl Parser {
    pub fn parse_expr(&mut self) -> Result<Expr> {
        self.parse_implies()
    }

    fn parse_implies(&mut self) -> Result<Expr> {
        self.parse_implication(Self::parse_or)
    }

    /// An implication over `operand`s, as TLA+ ranks them: `=>` binds looser than
    /// `<=>` and `~>`, which bind looser than the junctions `operand` parses. An
    /// operator at or left of the enclosing bullet column ends the expression, so
    /// it applies to the junction list the expression is an item of.
    fn parse_implication(&mut self, operand: fn(&mut Self) -> Result<Expr>) -> Result<Expr> {
        let mut left = self.parse_equivalence(operand)?;
        while *self.peek() == Token::Implies && !self.at_enclosing_bullet() {
            self.advance();
            let right = self.parse_equivalence(operand)?;
            left = Expr::Implies(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_equivalence(&mut self, operand: fn(&mut Self) -> Result<Expr>) -> Result<Expr> {
        let mut left = operand(self)?;
        loop {
            let combine: fn(Box<Expr>, Box<Expr>) -> Expr = match self.peek() {
                Token::Equiv => Expr::Equiv,
                Token::LeadsTo => Expr::LeadsTo,
                _ => break,
            };
            if self.at_enclosing_bullet() {
                break;
            }
            self.advance();
            let right = operand(self)?;
            left = combine(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    pub(super) fn consume_label(&mut self) -> Option<Arc<str>> {
        if let Token::Ident(name) = self.peek().clone()
            && *self.peek_n(1) == Token::LabelSep
        {
            self.advance();
            self.advance();
            return Some(name);
        }
        None
    }

    fn parse_or(&mut self) -> Result<Expr> {
        let bullet = if *self.peek() == Token::Or {
            let column = self.current_column();
            self.advance();
            self.consume_label();
            Some(column)
        } else {
            None
        };
        let mut infix_column = None;
        let mut item_line = self.current_line();
        let mut left = self.parse_or_item(bullet)?;
        while *self.peek() == Token::Or {
            if self.paren_depth == 0 && self.current_line() != item_line {
                let column = self.current_column();
                let ends_list = match (bullet, infix_column, self.list_col_stack.last()) {
                    (Some(bullet), _, _) => column < bullet,
                    (None, _, Some(&enclosing)) => column <= enclosing,
                    (None, Some(infix), None) => column != infix,
                    (None, None, None) => false,
                };
                if ends_list {
                    break;
                }
            }
            if bullet.is_none() && infix_column.is_none() {
                infix_column = Some(self.current_column());
            }
            self.advance();
            let label = self.consume_label();
            item_line = self.current_line();
            let right = self.parse_or_item(bullet)?;
            let right = wrap_with_label(right, label);
            left = Expr::Or(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_or_item(&mut self, bullet: Option<u32>) -> Result<Expr> {
        match bullet {
            Some(column) => self.parse_bullet_item(column),
            None => self.parse_and(),
        }
    }

    /// One item of a junction list whose bullet is at `column`: a whole expression,
    /// implications included, that ends at the first token at or left of `column`.
    pub(super) fn parse_bullet_item(&mut self, column: u32) -> Result<Expr> {
        self.list_col_stack.push(column);
        let item = self.parse_implies();
        self.list_col_stack.pop();
        item
    }

    /// Whether the current token, outside parentheses, sits at or left of the bullet
    /// column of the innermost junction list being parsed: there it ends the list's
    /// current item, so an operator such as `=>` takes the whole list as its left
    /// operand, as in SANY.
    fn at_enclosing_bullet(&self) -> bool {
        self.paren_depth == 0
            && self
                .list_col_stack
                .last()
                .is_some_and(|&bullet| self.current_column() <= bullet)
    }

    /// Whether the junction at the current token ends a nested body (a quantifier
    /// body, an `IF` branch) that began at `start_line`/`start_col`: inside a
    /// junction list, at or left of the innermost bullet column, as in SANY;
    /// elsewhere, on a later line left of the body's first token.
    fn ends_nested_body(&self, start_line: u32, start_col: u32) -> bool {
        match self.list_col_stack.last() {
            Some(&enclosing) => self.current_column() <= enclosing,
            None => self.current_line() != start_line && self.current_column() < start_col,
        }
    }

    pub(super) fn parse_and_conjunct(&mut self, list_col: Option<u32>) -> Result<Expr> {
        let mut result = self.parse_comparison()?;
        while *self.peek() == Token::And {
            if let Some(lc) = list_col
                && self.paren_depth == 0
                && self.current_column() <= lc
            {
                break;
            }
            if self.paren_depth == 0
                && let Some(&ec) = self.list_col_stack.last()
                && self.current_column() <= ec
            {
                break;
            }
            self.advance();
            let right = self.parse_comparison()?;
            result = Expr::And(Box::new(result), Box::new(right));
        }
        Ok(result)
    }

    fn parse_infix_and_operand(&mut self, list_col: u32) -> Result<Expr> {
        let start_line = self.current_line();
        let mut item = self.parse_and_conjunct(Some(list_col))?;
        while *self.peek() == Token::Or {
            if self.paren_depth == 0
                && self.current_line() != start_line
                && self.current_column() <= list_col
            {
                break;
            }
            self.advance();
            let label = self.consume_label();
            let right = self.parse_and_conjunct(Some(list_col))?;
            let right = wrap_with_label(right, label);
            item = Expr::Or(Box::new(item), Box::new(right));
        }
        Ok(item)
    }

    fn parse_and(&mut self) -> Result<Expr> {
        let mut list_anchor = None;
        if *self.peek() == Token::And {
            list_anchor = Some((self.current_column(), self.current_line()));
            self.advance();
            self.consume_label();
        }
        let bulleted = list_anchor.is_some();
        let mut left = if let Some((lc, _)) = list_anchor {
            self.parse_bullet_item(lc)?
        } else {
            self.parse_and_conjunct(None)?
        };
        loop {
            match self.peek() {
                Token::And => {
                    if self.paren_depth == 0
                        && let Some(&ec) = self.list_col_stack.last()
                        && self.current_column() <= ec
                    {
                        break;
                    }
                    if let Some((lc, _)) = list_anchor {
                        if self.paren_depth == 0 && self.current_column() != lc {
                            break;
                        }
                    } else {
                        list_anchor = Some((self.current_column(), self.current_line()));
                    }
                    self.advance();
                    let label = self.consume_label();
                    let right = match list_anchor {
                        Some((lc, _)) if bulleted => self.parse_bullet_item(lc)?,
                        Some((lc, _)) => self.parse_infix_and_operand(lc)?,
                        None => self.parse_and_conjunct(None)?,
                    };
                    let right = wrap_with_label(right, label);
                    left = Expr::And(Box::new(left), Box::new(right));
                }
                Token::ActionCompose => {
                    self.advance();
                    let right = self.parse_and_conjunct(list_anchor.map(|(c, _)| c))?;
                    left = Expr::ActionCompose(Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }
        Ok(left)
    }

    pub(super) fn parse_single_expr(&mut self) -> Result<Expr> {
        self.parse_single_implies()
    }

    fn parse_single_implies(&mut self) -> Result<Expr> {
        self.parse_implication(Self::parse_single_or)
    }

    fn parse_single_or(&mut self) -> Result<Expr> {
        let start_col = self.current_column();
        let start_line = self.current_line();
        let mut left = self.parse_single_and()?;
        while *self.peek() == Token::Or {
            if self.paren_depth == 0 && self.ends_nested_body(start_line, start_col) {
                break;
            }
            self.advance();
            let right = self.parse_single_and()?;
            left = Expr::Or(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_single_and(&mut self) -> Result<Expr> {
        if *self.peek() == Token::And {
            let anchor_col = self.current_column();
            self.advance();
            self.consume_label();
            let first_line = self.current_line();
            let mut left = self.parse_comparison()?;
            while *self.peek() == Token::And {
                let col = self.current_column();
                let line = self.current_line();
                if self.paren_depth == 0 && line != first_line && col != anchor_col {
                    break;
                }
                self.advance();
                let right = self.parse_comparison()?;
                left = Expr::And(Box::new(left), Box::new(right));
            }
            return Ok(left);
        }

        let start_col = self.current_column();
        let start_line = self.current_line();
        let mut left = self.parse_comparison()?;
        loop {
            match self.peek() {
                Token::And => {
                    if self.paren_depth == 0 && self.ends_nested_body(start_line, start_col) {
                        break;
                    }
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

    pub(super) fn parse_quantifier_body(&mut self) -> Result<Expr> {
        self.parse_implication(Self::parse_quantifier_or)
    }

    fn parse_quantifier_or(&mut self) -> Result<Expr> {
        let start_col = self.current_column();
        let start_line = self.current_line();
        let mut left = self.parse_quantifier_and()?;
        while *self.peek() == Token::Or {
            if self.paren_depth == 0 && self.ends_nested_body(start_line, start_col) {
                break;
            }
            self.advance();
            let right = self.parse_quantifier_and()?;
            left = Expr::Or(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_quantifier_and(&mut self) -> Result<Expr> {
        let start_col = self.current_column();
        let start_line = self.current_line();
        let mut left = self.parse_comparison()?;
        loop {
            match self.peek() {
                Token::And => {
                    if self.paren_depth == 0 && self.ends_nested_body(start_line, start_col) {
                        break;
                    }
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

    pub(super) fn parse_comparison(&mut self) -> Result<Expr> {
        if matches!(self.peek(), Token::Not) {
            self.advance();
            let expr = self.parse_comparison()?;
            return Ok(Expr::Not(Box::new(expr)));
        }
        let left = self.parse_fn_merge()?;
        match self.peek() {
            Token::Eq => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::Eq(Box::new(left), Box::new(right)))
            }
            Token::Neq => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::Neq(Box::new(left), Box::new(right)))
            }
            Token::Lt => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::Lt(Box::new(left), Box::new(right)))
            }
            Token::Le => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::Le(Box::new(left), Box::new(right)))
            }
            Token::Gt => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::Gt(Box::new(left), Box::new(right)))
            }
            Token::Ge => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::Ge(Box::new(left), Box::new(right)))
            }
            Token::In => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::In(Box::new(left), Box::new(right)))
            }
            Token::NotIn => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::NotIn(Box::new(left), Box::new(right)))
            }
            Token::Subseteq => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::Subset(Box::new(left), Box::new(right)))
            }
            Token::ProperSubset => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::ProperSubset(Box::new(left), Box::new(right)))
            }
            Token::Supseteq => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::Subset(Box::new(right), Box::new(left)))
            }
            Token::ProperSupset => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::ProperSubset(Box::new(right), Box::new(left)))
            }
            Token::SqSubseteq => {
                self.advance();
                let right = self.parse_fn_merge()?;
                Ok(Expr::SqSubseteq(Box::new(left), Box::new(right)))
            }
            _ => Ok(left),
        }
    }

    pub(super) fn parse_fn_merge(&mut self) -> Result<Expr> {
        let mut left = self.parse_maps_to()?;
        while *self.peek() == Token::AtAt {
            self.advance();
            let right = self.parse_maps_to()?;
            left = Expr::FnMerge(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_maps_to(&mut self) -> Result<Expr> {
        let left = self.parse_range()?;
        if *self.peek() == Token::ColonGt {
            self.advance();
            let right = self.parse_range()?;
            Ok(Expr::SingleFn(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    pub(super) fn parse_range(&mut self) -> Result<Expr> {
        let left = self.parse_additive()?;
        if *self.peek() == Token::DotDot {
            self.advance();
            let right = self.parse_additive()?;
            Ok(Expr::SetRange(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    pub(super) fn parse_additive(&mut self) -> Result<Expr> {
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
                    left = if self.user_infix_ops.contains("o") {
                        Expr::CustomOp(Arc::from("o"), Box::new(left), Box::new(right))
                    } else {
                        Expr::Concat(Box::new(left), Box::new(right))
                    };
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
                    left = if self.user_infix_ops.contains("oplus") {
                        Expr::CustomOp(Arc::from("oplus"), Box::new(left), Box::new(right))
                    } else {
                        Expr::BagAdd(Box::new(left), Box::new(right))
                    };
                }
                Token::BagSub => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = if self.user_infix_ops.contains("ominus") {
                        Expr::CustomOp(Arc::from("ominus"), Box::new(left), Box::new(right))
                    } else {
                        Expr::BagSub(Box::new(left), Box::new(right))
                    };
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
                Token::Slash if !self.warned_slash => {
                    self.warned_slash = true;
                    let span = self.current_span();
                    self.warnings.push(crate::span::Spanned::new(
                        "`/` is treated as integer division (like `\\div`); in TLA+ `/` is real \
                         division from the Reals module, which TLC cannot evaluate and tla-rs \
                         does not support — use `\\div` for integer division to silence this"
                            .to_string(),
                        span,
                    ));
                    self.advance();
                    let right = self.parse_exponential()?;
                    left = Expr::Div(Box::new(left), Box::new(right));
                }
                Token::Div | Token::Slash => {
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
                self.parse_postfix_ops(Expr::Cardinality(Box::new(expr)))
            }
            Token::IsFiniteSet => {
                self.advance();
                self.expect(Token::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::IsFiniteSet(Box::new(expr)))
            }
            Token::Len => {
                self.advance();
                self.expect(Token::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::Len(Box::new(expr)))
            }
            Token::Head => {
                self.advance();
                self.expect(Token::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::Head(Box::new(expr)))
            }
            Token::Tail => {
                self.advance();
                self.expect(Token::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::Tail(Box::new(expr)))
            }
            Token::Append => {
                self.advance();
                self.expect(Token::LParen)?;
                let seq = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let elem = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::Append(Box::new(seq), Box::new(elem)))
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
                self.parse_postfix_ops(Expr::SubSeq(Box::new(seq), Box::new(start), Box::new(end)))
            }
            Token::SelectSeq => {
                self.advance();
                self.expect(Token::LParen)?;
                let seq = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let test = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::SelectSeq(Box::new(seq), Box::new(test)))
            }
            Token::Seq => {
                self.advance();
                self.expect(Token::LParen)?;
                let domain = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::SeqSet(Box::new(domain)))
            }
            Token::Print => {
                self.advance();
                self.expect(Token::LParen)?;
                let val = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::Print(Box::new(val), Box::new(expr)))
            }
            Token::Assert => {
                self.advance();
                self.expect(Token::LParen)?;
                let cond = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let msg = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::Assert(Box::new(cond), Box::new(msg)))
            }
            Token::JavaTime => {
                self.advance();
                self.parse_postfix_ops(Expr::JavaTime)
            }
            Token::SystemTime => {
                self.advance();
                self.parse_postfix_ops(Expr::SystemTime)
            }
            Token::Permutations => {
                self.advance();
                self.expect(Token::LParen)?;
                let set = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::Permutations(Box::new(set)))
            }
            Token::SortSeq => {
                self.advance();
                self.expect(Token::LParen)?;
                let seq = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let cmp = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::SortSeq(Box::new(seq), Box::new(cmp)))
            }
            Token::PrintT => {
                self.advance();
                self.expect(Token::LParen)?;
                let val = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::PrintT(Box::new(val)))
            }
            Token::TLCToString => {
                self.advance();
                self.expect(Token::LParen)?;
                let val = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::TLCToString(Box::new(val)))
            }
            Token::RandomElement => {
                self.advance();
                self.expect(Token::LParen)?;
                let set = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::RandomElement(Box::new(set)))
            }
            Token::TLCGet => {
                self.advance();
                self.expect(Token::LParen)?;
                let idx = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::TLCGet(Box::new(idx)))
            }
            Token::TLCSet => {
                self.advance();
                self.expect(Token::LParen)?;
                let idx = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let val = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::TLCSet(Box::new(idx), Box::new(val)))
            }
            Token::Any => {
                self.advance();
                self.parse_postfix_ops(Expr::Any)
            }
            Token::TLCEval => {
                self.advance();
                self.expect(Token::LParen)?;
                let val = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::TLCEval(Box::new(val)))
            }
            Token::IsABag => {
                self.advance();
                self.expect(Token::LParen)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::IsABag(Box::new(bag)))
            }
            Token::BagToSet => {
                self.advance();
                self.expect(Token::LParen)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::BagToSet(Box::new(bag)))
            }
            Token::SetToBag => {
                self.advance();
                self.expect(Token::LParen)?;
                let set = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::SetToBag(Box::new(set)))
            }
            Token::BagIn => {
                self.advance();
                self.expect(Token::LParen)?;
                let elem = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::BagIn(Box::new(elem), Box::new(bag)))
            }
            Token::EmptyBag => {
                self.advance();
                self.parse_postfix_ops(Expr::EmptyBag)
            }
            Token::BagUnion => {
                self.advance();
                self.expect(Token::LParen)?;
                let bags = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::BagUnion(Box::new(bags)))
            }
            Token::SubBag => {
                self.advance();
                self.expect(Token::LParen)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::SubBag(Box::new(bag)))
            }
            Token::BagOfAll => {
                self.advance();
                self.expect(Token::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::BagOfAll(Box::new(expr), Box::new(bag)))
            }
            Token::BagCardinality => {
                self.advance();
                self.expect(Token::LParen)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::BagCardinality(Box::new(bag)))
            }
            Token::CopiesIn => {
                self.advance();
                self.expect(Token::LParen)?;
                let elem = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let bag = self.parse_expr()?;
                self.expect(Token::RParen)?;
                self.parse_postfix_ops(Expr::CopiesIn(Box::new(elem), Box::new(bag)))
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
                    let subscript = self.parse_subscript()?;
                    return Ok(Expr::BoxAction(Box::new(action), Box::new(subscript)));
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

    /// Distribute a prime over an expression: `(x >= 0)'` becomes `x' >= 0`.
    /// Every state-variable leaf is primed; constants and quantifier/`LET`-bound
    /// names are left rigid. Zero-arg operators are already inlined at their use
    /// sites, so `NonNegative'` reaches here as its body and primes correctly. A
    /// call left uninlined (to a `RECURSIVE` operator or an `INSTANCE`'s operator,
    /// say) is evaluated whole in the next state: priming its arguments alone would
    /// leave its body reading the current one.
    pub(super) fn prime_distribute(&self, expr: &Expr, bound: &mut Vec<Arc<str>>) -> Expr {
        use Expr::*;
        let un = |e: &Expr, b: &mut Vec<Arc<str>>| Box::new(self.prime_distribute(e, b));
        let binder = |s: &Self, n: &Arc<str>, dom: &Expr, body: &Expr, b: &mut Vec<Arc<str>>| {
            let d = Box::new(s.prime_distribute(dom, b));
            b.push(n.clone());
            let body = Box::new(s.prime_distribute(body, b));
            b.pop();
            (d, body)
        };
        match expr {
            Var(v) => {
                if bound.iter().any(|x| x == v) || self.constants.iter().any(|c| c == v) {
                    Var(v.clone())
                } else {
                    Prime(v.clone())
                }
            }
            Prime(v) => Prime(v.clone()),
            Lit(x) => Lit(x.clone()),
            OldValue => OldValue,
            JavaTime => JavaTime,
            SystemTime => SystemTime,
            Any => Any,
            EmptyBag => EmptyBag,
            Unchanged(vs) => Unchanged(vs.clone()),

            Not(e) => Not(un(e, bound)),
            Neg(e) => Neg(un(e, bound)),
            TransitiveClosure(e) => TransitiveClosure(un(e, bound)),
            ReflexiveTransitiveClosure(e) => ReflexiveTransitiveClosure(un(e, bound)),
            Powerset(e) => Powerset(un(e, bound)),
            Cardinality(e) => Cardinality(un(e, bound)),
            IsFiniteSet(e) => IsFiniteSet(un(e, bound)),
            BigUnion(e) => BigUnion(un(e, bound)),
            Domain(e) => Domain(un(e, bound)),
            Len(e) => Len(un(e, bound)),
            Head(e) => Head(un(e, bound)),
            Tail(e) => Tail(un(e, bound)),
            SeqSet(e) => SeqSet(un(e, bound)),
            PrintT(e) => PrintT(un(e, bound)),
            Permutations(e) => Permutations(un(e, bound)),
            TLCToString(e) => TLCToString(un(e, bound)),
            RandomElement(e) => RandomElement(un(e, bound)),
            TLCGet(e) => TLCGet(un(e, bound)),
            TLCEval(e) => TLCEval(un(e, bound)),
            IsABag(e) => IsABag(un(e, bound)),
            BagToSet(e) => BagToSet(un(e, bound)),
            SetToBag(e) => SetToBag(un(e, bound)),
            BagUnion(e) => BagUnion(un(e, bound)),
            SubBag(e) => SubBag(un(e, bound)),
            BagCardinality(e) => BagCardinality(un(e, bound)),
            Always(e) => Always(un(e, bound)),
            Eventually(e) => Eventually(un(e, bound)),
            EnabledOp(e) => EnabledOp(un(e, bound)),

            And(l, r) => And(un(l, bound), un(r, bound)),
            Or(l, r) => Or(un(l, bound), un(r, bound)),
            Implies(l, r) => Implies(un(l, bound), un(r, bound)),
            Equiv(l, r) => Equiv(un(l, bound), un(r, bound)),
            Eq(l, r) => Eq(un(l, bound), un(r, bound)),
            Neq(l, r) => Neq(un(l, bound), un(r, bound)),
            In(l, r) => In(un(l, bound), un(r, bound)),
            NotIn(l, r) => NotIn(un(l, bound), un(r, bound)),
            Add(l, r) => Add(un(l, bound), un(r, bound)),
            Sub(l, r) => Sub(un(l, bound), un(r, bound)),
            Mul(l, r) => Mul(un(l, bound), un(r, bound)),
            Div(l, r) => Div(un(l, bound), un(r, bound)),
            Mod(l, r) => Mod(un(l, bound), un(r, bound)),
            Exp(l, r) => Exp(un(l, bound), un(r, bound)),
            BitwiseAnd(l, r) => BitwiseAnd(un(l, bound), un(r, bound)),
            ActionCompose(l, r) => ActionCompose(un(l, bound), un(r, bound)),
            Lt(l, r) => Lt(un(l, bound), un(r, bound)),
            Le(l, r) => Le(un(l, bound), un(r, bound)),
            Gt(l, r) => Gt(un(l, bound), un(r, bound)),
            Ge(l, r) => Ge(un(l, bound), un(r, bound)),
            SetRange(l, r) => SetRange(un(l, bound), un(r, bound)),
            Union(l, r) => Union(un(l, bound), un(r, bound)),
            Intersect(l, r) => Intersect(un(l, bound), un(r, bound)),
            SetMinus(l, r) => SetMinus(un(l, bound), un(r, bound)),
            Cartesian(l, r) => Cartesian(un(l, bound), un(r, bound)),
            Subset(l, r) => Subset(un(l, bound), un(r, bound)),
            ProperSubset(l, r) => ProperSubset(un(l, bound), un(r, bound)),
            FnApp(l, r) => FnApp(un(l, bound), un(r, bound)),
            FnMerge(l, r) => FnMerge(un(l, bound), un(r, bound)),
            SingleFn(l, r) => SingleFn(un(l, bound), un(r, bound)),
            FunctionSet(l, r) => FunctionSet(un(l, bound), un(r, bound)),
            Append(l, r) => Append(un(l, bound), un(r, bound)),
            Concat(l, r) => Concat(un(l, bound), un(r, bound)),
            SelectSeq(l, r) => SelectSeq(un(l, bound), un(r, bound)),
            Print(l, r) => Print(un(l, bound), un(r, bound)),
            Assert(l, r) => Assert(un(l, bound), un(r, bound)),
            TLCSet(l, r) => TLCSet(un(l, bound), un(r, bound)),
            SortSeq(l, r) => SortSeq(un(l, bound), un(r, bound)),
            BagIn(l, r) => BagIn(un(l, bound), un(r, bound)),
            BagAdd(l, r) => BagAdd(un(l, bound), un(r, bound)),
            BagSub(l, r) => BagSub(un(l, bound), un(r, bound)),
            SqSubseteq(l, r) => SqSubseteq(un(l, bound), un(r, bound)),
            BagOfAll(l, r) => BagOfAll(un(l, bound), un(r, bound)),
            CopiesIn(l, r) => CopiesIn(un(l, bound), un(r, bound)),
            LeadsTo(l, r) => LeadsTo(un(l, bound), un(r, bound)),

            If(c, t, e) => If(un(c, bound), un(t, bound), un(e, bound)),
            SubSeq(a, b, c) => SubSeq(un(a, bound), un(b, bound), un(c, bound)),

            Exists(n, d, b) => {
                let (d, b) = binder(self, n, d, b, bound);
                Exists(n.clone(), d, b)
            }
            Forall(n, d, b) => {
                let (d, b) = binder(self, n, d, b, bound);
                Forall(n.clone(), d, b)
            }
            Choose(n, d, b) => {
                let (d, b) = binder(self, n, d, b, bound);
                Choose(n.clone(), d, b)
            }
            FnDef(n, d, b) => {
                let (d, b) = binder(self, n, d, b, bound);
                FnDef(n.clone(), d, b)
            }
            SetFilter(n, d, b) => {
                let (d, b) = binder(self, n, d, b, bound);
                SetFilter(n.clone(), d, b)
            }
            SetMap(n, d, b) => {
                let (d, b) = binder(self, n, d, b, bound);
                SetMap(n.clone(), d, b)
            }
            CustomOp(n, d, b) => {
                let (d, b) = binder(self, n, d, b, bound);
                CustomOp(n.clone(), d, b)
            }
            ChooseUnbounded(n, b) => {
                bound.push(n.clone());
                let body = Box::new(self.prime_distribute(b, bound));
                bound.pop();
                ChooseUnbounded(n.clone(), body)
            }
            Lambda(params, b) => {
                for p in params {
                    bound.push(p.clone());
                }
                let body = Box::new(self.prime_distribute(b, bound));
                for _ in params {
                    bound.pop();
                }
                Lambda(params.clone(), body)
            }
            Let(n, binding, body) => {
                let binding = un(binding, bound);
                bound.push(n.clone());
                let body = Box::new(self.prime_distribute(body, bound));
                bound.pop();
                Let(n.clone(), binding, body)
            }

            SetEnum(elems) => SetEnum(
                elems
                    .iter()
                    .map(|e| self.prime_distribute(e, bound))
                    .collect(),
            ),
            TupleLit(elems) => TupleLit(
                elems
                    .iter()
                    .map(|e| self.prime_distribute(e, bound))
                    .collect(),
            ),
            RecordLit(fields) => RecordLit(
                fields
                    .iter()
                    .map(|(k, e)| (k.clone(), self.prime_distribute(e, bound)))
                    .collect(),
            ),
            RecordSet(fields) => RecordSet(
                fields
                    .iter()
                    .map(|(k, e)| (k.clone(), self.prime_distribute(e, bound)))
                    .collect(),
            ),
            RecordAccess(e, f) => RecordAccess(un(e, bound), f.clone()),
            TupleAccess(e, i) => TupleAccess(un(e, bound), *i),
            Except(base, updates) => Except(
                un(base, bound),
                updates
                    .iter()
                    .map(|(path, val)| {
                        (
                            path.iter()
                                .map(|p| self.prime_distribute(p, bound))
                                .collect(),
                            self.prime_distribute(val, bound),
                        )
                    })
                    .collect(),
            ),
            FnCall(_, _) => primed_application(expr),
            QualifiedCall(_, _, _) => primed_application(expr),
            Case(branches) => Case(
                branches
                    .iter()
                    .map(|(c, r)| {
                        (
                            self.prime_distribute(c, bound),
                            self.prime_distribute(r, bound),
                        )
                    })
                    .collect(),
            ),
            LabeledAction(n, a) => LabeledAction(n.clone(), un(a, bound)),
            WeakFairness(v, e) => WeakFairness(un(v, bound), un(e, bound)),
            StrongFairness(v, e) => StrongFairness(un(v, bound), un(e, bound)),
            BoxAction(e, v) => BoxAction(un(e, bound), un(v, bound)),
            DiamondAction(e, v) => DiamondAction(un(e, bound), un(v, bound)),
        }
    }

    fn parse_postfix(&mut self) -> Result<Expr> {
        let expr = self.parse_primary()?;
        self.parse_postfix_ops(expr)
    }

    /// The primes, function applications `[e]` and record accesses `.f` that
    /// follow `expr`, applied left to right.
    fn parse_postfix_ops(&mut self, mut expr: Expr) -> Result<Expr> {
        loop {
            match self.peek() {
                Token::Prime => {
                    self.advance();
                    expr = self.prime_distribute(&expr, &mut Vec::new());
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
                Token::Bang => {
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
                    expr = Expr::QualifiedCall(Box::new(expr), op_name, args);
                }
                _ => break,
            }
        }
        Ok(expr)
    }
}

pub(super) fn wrap_with_label(expr: Expr, label: Option<Arc<str>>) -> Expr {
    match label {
        Some(name) => Expr::LabeledAction(name, Box::new(expr)),
        None => expr,
    }
}

/// `Op(args)'` (or `I!Op(args)'`) as `LET $primed == Op(args) IN $primed'`: priming an operator with
/// no parameters evaluates its body in the next state, the arguments and every
/// state variable the operator reads included. `$` cannot appear in an identifier,
/// so the name shadows nothing a spec defines.
fn primed_application(call: &Expr) -> Expr {
    let name: Arc<str> = Arc::from("$primed");
    let operator = Expr::Let(
        Arc::from("_params"),
        Box::new(Expr::TupleLit(Vec::new())),
        Box::new(call.clone()),
    );
    Expr::Let(
        name.clone(),
        Box::new(operator),
        Box::new(Expr::Prime(name)),
    )
}
