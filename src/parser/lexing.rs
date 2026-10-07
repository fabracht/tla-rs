use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::ast::{Expr, FairnessConstraint, InstanceDecl, LivenessProperty};
use crate::lexer::{Lexer, Token};
use crate::source::Source;
use crate::span::{Span, Spanned};

use super::error::{ParseError, Result};

pub struct Parser {
    pub(super) tokens: Vec<Spanned<Token>>,
    pub(super) pos: usize,
    pub(super) paren_depth: u32,
    pub(super) definitions: BTreeMap<Arc<str>, Expr>,
    pub(super) fn_definitions: BTreeMap<Arc<str>, (Vec<Arc<str>>, Expr)>,
    pub(super) recursive_names: BTreeSet<Arc<str>>,
    pub(super) constants: Vec<Arc<str>>,
    pub(super) extends: Vec<Arc<str>>,
    pub(super) assumes: Vec<Expr>,
    pub(super) instances: Vec<InstanceDecl>,
    pub(super) fairness: Vec<FairnessConstraint>,
    pub(super) liveness_properties: Vec<LivenessProperty>,
    pub(super) quantified_fairness: Vec<(Arc<str>, Expr, Expr)>,
    pub(super) warnings: Vec<Spanned<String>>,
    pub(super) fresh_counter: u64,
    /// The source text with its precomputed line-start index, so `line_of` and
    /// `column_of` resolve a byte offset by binary search instead of rescanning
    /// from the start on every token — the difference between O(n) and O(n²)
    /// parsing over a large module.
    pub(super) source: Source,
    /// Names bound by an enclosing `LET`. An operator reference whose name is in
    /// scope here must not be inlined from the top-level definitions — the local
    /// `LET` binding shadows it, and inlining would use the wrong (top-level) body.
    pub(super) let_scope: Vec<Arc<str>>,
    /// Bullet columns of the junction lists whose items are currently being
    /// parsed, innermost last. A token at or left of the innermost column ends the
    /// current item, so a nested expression — a `LET` body, an `IF` branch, an
    /// implication — stops there instead of swallowing the next bullet of an
    /// enclosing list or the operator the list is an operand of. Alignment does not
    /// apply inside parentheses: the stack is kept there, and readers check
    /// `paren_depth` before using it.
    pub(super) list_col_stack: Vec<u32>,
    /// Whether the `/`-is-integer-division warning has already been emitted, so a
    /// spec with many `/` uses gets one warning, not one per occurrence.
    pub(super) warned_slash: bool,
    /// Canonical names of infix operators the module defines itself (e.g. `oplus`
    /// from `a \oplus b == ...`). A use of such a symbol resolves to the user
    /// definition instead of the built-in, shadowing it within the module.
    pub(super) user_infix_ops: BTreeSet<Arc<str>>,
}

impl Parser {
    pub fn new(input: &str) -> Result<Self> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize_spanned()?;
        Ok(Self {
            tokens,
            pos: 0,
            source: Source::new("", input),
            paren_depth: 0,
            definitions: BTreeMap::new(),
            fn_definitions: BTreeMap::new(),
            recursive_names: BTreeSet::new(),
            constants: Vec::new(),
            extends: Vec::new(),
            assumes: Vec::new(),
            instances: Vec::new(),
            fairness: Vec::new(),
            liveness_properties: Vec::new(),
            quantified_fairness: Vec::new(),
            warnings: Vec::new(),
            fresh_counter: 0,
            let_scope: Vec::new(),
            list_col_stack: Vec::new(),
            warned_slash: false,
            user_infix_ops: BTreeSet::new(),
        })
    }

    pub(super) fn fresh_tuple_name(&mut self) -> Arc<str> {
        let n = self.fresh_counter;
        self.fresh_counter += 1;
        format!("__tup_{}", n).into()
    }

    pub fn warnings(&self) -> &[Spanned<String>] {
        &self.warnings
    }

    pub fn take_warnings(&mut self) -> Vec<Spanned<String>> {
        std::mem::take(&mut self.warnings)
    }

    pub(super) fn column_of(&self, byte_offset: u32) -> u32 {
        self.source.line_col(byte_offset).1 as u32 - 1
    }

    pub(super) fn line_of(&self, byte_offset: u32) -> u32 {
        self.source.line_col(byte_offset).0 as u32 - 1
    }

    pub(super) fn current_column(&self) -> u32 {
        self.column_of(self.current_span().start)
    }

    pub(super) fn current_line(&self) -> u32 {
        self.line_of(self.current_span().start)
    }

    pub(super) fn col_mismatch(&self, list_col: u32, list_line: u32) -> bool {
        if self.paren_depth > 0 {
            return false;
        }
        let col = self.current_column();
        let line = self.current_line();
        line != list_line && col != list_col
    }

    pub(super) fn peek(&self) -> &Token {
        self.tokens
            .get(self.pos)
            .map(|t| &t.value)
            .unwrap_or(&Token::Eof)
    }

    pub(super) fn peek_n(&self, n: usize) -> &Token {
        self.tokens
            .get(self.pos + n)
            .map(|t| &t.value)
            .unwrap_or(&Token::Eof)
    }

    pub(super) fn current_span(&self) -> Span {
        self.tokens
            .get(self.pos)
            .map(|t| t.span)
            .unwrap_or(Span::empty())
    }

    pub(super) fn is_module_prefix(s: &str) -> bool {
        !s.is_empty() && (s.chars().all(|c| c.is_ascii_uppercase()) || s.ends_with('_'))
    }

    /// Whether `name` is detected as the spec's `role` (`Init` or `Next`): the
    /// name itself or a module prefix followed by it (`TPInit`, `M_Next`).
    pub(crate) fn is_behavior_name(name: &str, role: &str) -> bool {
        name == role || name.strip_suffix(role).is_some_and(Self::is_module_prefix)
    }

    pub(super) fn is_invariant_name(name: &str) -> bool {
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

    pub(super) fn advance(&mut self) -> Token {
        let tok = self.peek().clone();
        if tok != Token::Eof {
            self.pos += 1;
        }
        tok
    }

    pub(super) fn expect(&mut self, expected: Token) -> Result<()> {
        let span = self.current_span();
        let tok = self.advance();
        if tok == expected {
            Ok(())
        } else {
            Err(ParseError::new(format!("unexpected {tok}"))
                .with_span(span)
                .with_context(format!("{expected}"), format!("{tok}")))
        }
    }

    pub(super) fn expect_ident(&mut self) -> Result<Arc<str>> {
        let span = self.current_span();
        match self.advance() {
            Token::Ident(s) => Ok(s),
            other => Err(ParseError::new(format!("unexpected {other}"))
                .with_span(span)
                .with_context("identifier", format!("{other}"))),
        }
    }

    /// Skips a theorem or proof up to the next unit. An `ASSUME ... PROVE` in it is
    /// part of the proof, not a module `ASSUME`.
    pub(super) fn skip_to_next_definition(&mut self) {
        while !self.at_unit_start() || (*self.peek() == Token::Assume && self.assume_has_prove()) {
            self.advance();
        }
    }

    /// Skips the rest of a definition that did not parse, from the token after its
    /// name. While a `LET` the failed body opened is open, what starts right of
    /// `column`, the failed definition's own, belongs to it; a unit at or left of it
    /// ends the skip even then (a body whose `IN` is missing).
    pub(super) fn skip_failed_definition(&mut self, column: u32) {
        while !matches!(self.peek(), Token::EqEq | Token::Eof) {
            self.advance();
        }
        self.advance();
        if *self.peek() == Token::Instance {
            self.advance();
        }
        let mut open_lets = 0usize;
        loop {
            let belongs_to_body =
                open_lets > 0 && self.column_of(self.current_span().start) > column;
            if *self.peek() == Token::Eof || (self.at_unit_start() && !belongs_to_body) {
                return;
            }
            match self.advance() {
                Token::Let => open_lets += 1,
                Token::Def => open_lets = open_lets.saturating_sub(1),
                _ => {}
            }
        }
    }

    /// A separator the top level skips between units.
    pub(super) fn is_separator(token: &Token) -> bool {
        matches!(
            token,
            Token::Semicolon | Token::Dollar | Token::Pipe | Token::Caret | Token::Ampersand
        )
    }

    /// Whether a `PROVE` follows the `ASSUME` at the current position before the
    /// next unit, making it an `ASSUME ... PROVE` statement of a proof.
    fn assume_has_prove(&self) -> bool {
        for (index, token) in self.tokens.iter().enumerate().skip(self.pos + 1) {
            match &token.value {
                Token::Prove => return true,
                Token::Eof
                | Token::Module
                | Token::Extends
                | Token::Variables
                | Token::Constants
                | Token::Assume
                | Token::Theorem
                | Token::Lemma
                | Token::ProofStep
                | Token::Qed
                | Token::ProofDef
                | Token::Recursive
                | Token::Local
                | Token::Instance
                | Token::Invariant => return false,
                Token::Ident(_)
                    if matches!(
                        self.tokens.get(index + 1).map(|next| &next.value),
                        Some(Token::EqEq)
                    ) =>
                {
                    return false;
                }
                _ => {}
            }
        }
        false
    }

    /// Whether the next token starts a module unit: a declaration, an `ASSUME`,
    /// `THEOREM` or proof step, or a definition (`Name ==`, `Name(...) ==`,
    /// `f[...] ==` or `a \op b ==`).
    pub(super) fn at_unit_start(&self) -> bool {
        match self.peek() {
            Token::Eof
            | Token::Module
            | Token::Extends
            | Token::Variables
            | Token::Constants
            | Token::Assume
            | Token::Theorem
            | Token::Recursive
            | Token::Local
            | Token::Instance
            | Token::Lemma
            | Token::ProofStep
            | Token::By
            | Token::Prove
            | Token::Qed
            | Token::ProofDef
            | Token::Invariant => true,
            Token::Ident(_) => match self.peek_n(1) {
                Token::EqEq => true,
                Token::LParen => self.group_then_eqeq(self.pos + 1, &Token::LParen, &Token::RParen),
                Token::LBracket => {
                    self.group_then_eqeq(self.pos + 1, &Token::LBracket, &Token::RBracket)
                }
                tok => {
                    Self::infix_op_name(tok).is_some()
                        && matches!(self.peek_n(2), Token::Ident(_))
                        && *self.peek_n(3) == Token::EqEq
                }
            },
            _ => false,
        }
    }

    fn group_then_eqeq(&self, open: usize, opening: &Token, closing: &Token) -> bool {
        let mut depth = 0usize;
        for (index, token) in self.tokens.iter().enumerate().skip(open) {
            if token.value == *opening {
                depth += 1;
            } else if token.value == *closing {
                depth -= 1;
                if depth == 0 {
                    return self
                        .tokens
                        .get(index + 1)
                        .is_some_and(|next| next.value == Token::EqEq);
                }
            } else if token.value == Token::Eof {
                return false;
            }
        }
        false
    }
}
