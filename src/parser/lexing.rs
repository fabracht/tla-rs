use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::ast::{Expr, FairnessConstraint, InstanceDecl};
use crate::lexer::{Lexer, Token};
use crate::span::{Span, Spanned};

use super::error::{ParseError, Result};

pub struct Parser {
    pub(super) tokens: Vec<Spanned<Token>>,
    pub(super) pos: usize,
    pub(super) source: Arc<str>,
    pub(super) paren_depth: u32,
    pub(super) definitions: BTreeMap<Arc<str>, Expr>,
    pub(super) fn_definitions: BTreeMap<Arc<str>, (Vec<Arc<str>>, Expr)>,
    pub(super) recursive_names: BTreeSet<Arc<str>>,
    pub(super) constants: Vec<Arc<str>>,
    pub(super) extends: Vec<Arc<str>>,
    pub(super) assumes: Vec<Expr>,
    pub(super) instances: Vec<InstanceDecl>,
    pub(super) fairness: Vec<FairnessConstraint>,
    pub(super) liveness_properties: Vec<Expr>,
}

impl Parser {
    pub fn new(input: &str) -> Result<Self> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize_spanned()?;
        Ok(Self {
            tokens,
            pos: 0,
            source: Arc::from(input),
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
        })
    }

    pub(super) fn column_of(&self, byte_offset: u32) -> u32 {
        let offset = byte_offset as usize;
        let src = &self.source[..offset.min(self.source.len())];
        match src.rfind('\n') {
            Some(nl) => (offset - nl - 1) as u32,
            None => offset as u32,
        }
    }

    pub(super) fn line_of(&self, byte_offset: u32) -> u32 {
        let offset = byte_offset as usize;
        self.source[..offset.min(self.source.len())]
            .bytes()
            .filter(|&b| b == b'\n')
            .count() as u32
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

    pub(super) fn prev_span(&self) -> Span {
        if self.pos > 0 {
            self.tokens
                .get(self.pos - 1)
                .map(|t| t.span)
                .unwrap_or(Span::empty())
        } else {
            Span::empty()
        }
    }

    pub(super) fn is_module_prefix(s: &str) -> bool {
        !s.is_empty() && (s.chars().all(|c| c.is_ascii_uppercase()) || s.ends_with('_'))
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

    pub(super) fn skip_to_next_definition(&mut self) {
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
}
