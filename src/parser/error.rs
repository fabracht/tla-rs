use crate::lexer::LexError;
use crate::span::Span;

#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub span: Option<Span>,
    pub expected: Option<String>,
    pub found: Option<String>,
    pub help: Option<String>,
}

impl ParseError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            span: None,
            expected: None,
            found: None,
            help: None,
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

    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)?;
        if let (Some(expected), Some(found)) = (&self.expected, &self.found) {
            write!(f, " (expected {expected}, found {found})")?;
        }
        Ok(())
    }
}

impl std::error::Error for ParseError {}

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

pub(crate) type Result<T> = std::result::Result<T, ParseError>;
