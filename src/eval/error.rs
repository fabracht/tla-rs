use std::fmt;
use std::sync::Arc;

use crate::ast::{Env, Value};
use crate::diagnostic::find_similar;
use crate::span::Span;

use super::Definitions;

#[derive(Debug, Clone)]
pub enum EvalError {
    UndefinedVar {
        name: Arc<str>,
        suggestion: Option<Arc<str>>,
        span: Option<Span>,
    },
    TypeMismatch {
        expected: &'static str,
        got: Value,
        context: Option<&'static str>,
        span: Option<Span>,
    },
    DivisionByZero {
        span: Option<Span>,
    },
    EmptyChoose {
        span: Option<Span>,
    },
    DomainError {
        message: String,
        span: Option<Span>,
    },
}

impl EvalError {
    pub fn undefined_var(name: Arc<str>) -> Self {
        Self::UndefinedVar {
            name,
            suggestion: None,
            span: None,
        }
    }

    pub fn undefined_var_with_env(name: Arc<str>, env: &Env, defs: &Definitions) -> Self {
        let candidates = env
            .keys()
            .map(|s| s.as_ref())
            .chain(defs.keys().map(|s| s.as_ref()));
        let suggestion = find_similar(&name, candidates, 2).map(|s| s.into());
        Self::UndefinedVar {
            name,
            suggestion,
            span: None,
        }
    }

    pub fn type_mismatch(expected: &'static str, got: Value) -> Self {
        Self::TypeMismatch {
            expected,
            got,
            context: None,
            span: None,
        }
    }

    pub fn type_mismatch_ctx(expected: &'static str, got: Value, context: &'static str) -> Self {
        Self::TypeMismatch {
            expected,
            got,
            context: Some(context),
            span: None,
        }
    }

    pub fn division_by_zero() -> Self {
        Self::DivisionByZero { span: None }
    }

    pub fn empty_choose() -> Self {
        Self::EmptyChoose { span: None }
    }

    pub fn domain_error(msg: impl Into<String>) -> Self {
        Self::DomainError {
            message: msg.into(),
            span: None,
        }
    }

    pub fn with_span(mut self, span: Span) -> Self {
        match &mut self {
            Self::UndefinedVar { span: s, .. }
            | Self::TypeMismatch { span: s, .. }
            | Self::DivisionByZero { span: s }
            | Self::EmptyChoose { span: s }
            | Self::DomainError { span: s, .. } => *s = Some(span),
        }
        self
    }

    pub fn span(&self) -> Option<Span> {
        match self {
            Self::UndefinedVar { span, .. }
            | Self::TypeMismatch { span, .. }
            | Self::DivisionByZero { span }
            | Self::EmptyChoose { span }
            | Self::DomainError { span, .. } => *span,
        }
    }
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UndefinedVar {
                name, suggestion, ..
            } => {
                write!(f, "undefined variable '{name}'")?;
                if let Some(s) = suggestion {
                    write!(f, ", did you mean '{s}'?")?;
                }
                Ok(())
            }
            Self::TypeMismatch {
                expected,
                got,
                context,
                ..
            } => {
                write!(
                    f,
                    "type mismatch: expected {expected}, got {}",
                    value_type_name(got)
                )?;
                if let Some(ctx) = context {
                    write!(f, " in {ctx}")?;
                }
                Ok(())
            }
            Self::DivisionByZero { .. } => write!(f, "division by zero"),
            Self::EmptyChoose { .. } => write!(f, "CHOOSE found no matching value"),
            Self::DomainError { message, .. } => write!(f, "{message}"),
        }
    }
}

impl std::error::Error for EvalError {}

pub(crate) type Result<T> = std::result::Result<T, EvalError>;

pub(crate) fn value_type_name(val: &Value) -> &'static str {
    match val {
        Value::Bool(_) => "Bool",
        Value::Int(_) => "Int",
        Value::Str(_) => "Str",
        Value::Set(_) => "Set",
        Value::Fn(_) => "Function",
        Value::Record(_) => "Record",
        Value::Tuple(_) => "Sequence",
    }
}
