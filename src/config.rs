use std::collections::BTreeSet;
use std::sync::Arc;

use crate::ast::{Env, Expr, Spec, Value};
use crate::checker::CheckerConfig;

#[derive(Debug)]
pub struct TlcConfig {
    pub init: Option<Arc<str>>,
    pub next: Option<Arc<str>>,
    pub specification: Option<Arc<str>>,
    pub constants: Vec<(Arc<str>, Value)>,
    pub invariants: Vec<Arc<str>>,
    pub properties: Vec<Arc<str>>,
    pub symmetry: Option<Arc<str>>,
    pub check_deadlock: Option<bool>,
    pub constraints: Vec<Arc<str>>,
    pub action_constraints: Vec<Arc<str>>,
}

impl TlcConfig {
    fn new() -> Self {
        Self {
            init: None,
            next: None,
            specification: None,
            constants: Vec::new(),
            invariants: Vec::new(),
            properties: Vec::new(),
            symmetry: None,
            check_deadlock: None,
            constraints: Vec::new(),
            action_constraints: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Keyword(String),
    Ident(String),
    Int(i64),
    Str(String),
    Eq,
    LBrace,
    RBrace,
    Comma,
}

fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = input.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        if chars[i].is_ascii_whitespace() {
            i += 1;
            continue;
        }

        if chars[i] == '\\' && i + 1 < chars.len() && chars[i + 1] == '*' {
            i += 2;
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }

        if chars[i] == '(' && i + 1 < chars.len() && chars[i + 1] == '*' {
            i += 2;
            loop {
                if i + 1 >= chars.len() {
                    return Err("unterminated block comment".to_string());
                }
                if chars[i] == '*' && chars[i + 1] == ')' {
                    i += 2;
                    break;
                }
                i += 1;
            }
            continue;
        }

        if chars[i] == '=' {
            tokens.push(Token::Eq);
            i += 1;
            continue;
        }

        if chars[i] == '{' {
            tokens.push(Token::LBrace);
            i += 1;
            continue;
        }

        if chars[i] == '}' {
            tokens.push(Token::RBrace);
            i += 1;
            continue;
        }

        if chars[i] == ',' {
            tokens.push(Token::Comma);
            i += 1;
            continue;
        }

        if chars[i] == '"' {
            i += 1;
            let mut s = String::new();
            while i < chars.len() && chars[i] != '"' {
                if chars[i] == '\\' && i + 1 < chars.len() {
                    s.push(chars[i]);
                    s.push(chars[i + 1]);
                    i += 2;
                    continue;
                }
                s.push(chars[i]);
                i += 1;
            }
            if i >= chars.len() {
                return Err("unterminated string literal".to_string());
            }
            i += 1;
            tokens.push(Token::Str(s));
            continue;
        }

        if chars[i] == '-' && i + 1 < chars.len() && chars[i + 1].is_ascii_digit() {
            i += 1;
            let mut num = String::new();
            while i < chars.len() && chars[i].is_ascii_digit() {
                num.push(chars[i]);
                i += 1;
            }
            let n: i64 = num
                .parse()
                .map_err(|_| format!("invalid integer: -{}", num))?;
            tokens.push(Token::Int(-n));
            continue;
        }

        if chars[i].is_ascii_digit() {
            let mut num = String::new();
            while i < chars.len() && chars[i].is_ascii_digit() {
                num.push(chars[i]);
                i += 1;
            }
            let n: i64 = num
                .parse()
                .map_err(|_| format!("invalid integer: {}", num))?;
            tokens.push(Token::Int(n));
            continue;
        }

        if chars[i].is_ascii_alphabetic() || chars[i] == '_' {
            let mut word = String::new();
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                word.push(chars[i]);
                i += 1;
            }
            let is_keyword = matches!(
                word.as_str(),
                "INIT"
                    | "NEXT"
                    | "SPECIFICATION"
                    | "CONSTANT"
                    | "CONSTANTS"
                    | "INVARIANT"
                    | "INVARIANTS"
                    | "PROPERTY"
                    | "PROPERTIES"
                    | "SYMMETRY"
                    | "CHECK_DEADLOCK"
                    | "CONSTRAINT"
                    | "CONSTRAINTS"
                    | "ACTION_CONSTRAINT"
                    | "ACTION_CONSTRAINTS"
            );
            if is_keyword {
                tokens.push(Token::Keyword(word));
            } else {
                tokens.push(Token::Ident(word));
            }
            continue;
        }

        return Err(format!("unexpected character: '{}'", chars[i]));
    }

    Ok(tokens)
}

fn is_keyword(tok: &Token) -> bool {
    matches!(tok, Token::Keyword(_))
}

fn parse_constant_value_from_tokens(tokens: &[Token], pos: &mut usize) -> Result<Value, String> {
    if *pos >= tokens.len() {
        return Err("expected value, got end of input".to_string());
    }

    match &tokens[*pos] {
        Token::Int(n) => {
            let val = Value::Int(*n);
            *pos += 1;
            Ok(val)
        }
        Token::Str(s) => {
            let val = Value::Str(Arc::from(s.as_str()));
            *pos += 1;
            Ok(val)
        }
        Token::Ident(s) if s == "TRUE" => {
            *pos += 1;
            Ok(Value::Bool(true))
        }
        Token::Ident(s) if s == "FALSE" => {
            *pos += 1;
            Ok(Value::Bool(false))
        }
        Token::LBrace => {
            *pos += 1;
            let mut set = BTreeSet::new();
            if *pos < tokens.len() && tokens[*pos] == Token::RBrace {
                *pos += 1;
                return Ok(Value::Set(set));
            }
            loop {
                let val = parse_constant_value_from_tokens(tokens, pos)?;
                set.insert(val);
                if *pos >= tokens.len() {
                    return Err("expected '}' or ','".to_string());
                }
                if tokens[*pos] == Token::RBrace {
                    *pos += 1;
                    break;
                }
                if tokens[*pos] == Token::Comma {
                    *pos += 1;
                } else {
                    return Err(format!("expected ',' or '}}', got {:?}", tokens[*pos]));
                }
            }
            Ok(Value::Set(set))
        }
        Token::Ident(s) => {
            let val = Value::Str(Arc::from(s.as_str()));
            *pos += 1;
            Ok(val)
        }
        other => Err(format!("expected value, got {:?}", other)),
    }
}

pub fn split_top_level(s: &str, delim: char) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth: u32 = 0;
    let mut in_string = false;
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        let c = chars[i];
        if in_string {
            if c == '\\' && i + 1 < chars.len() {
                current.push(c);
                current.push(chars[i + 1]);
                i += 2;
                continue;
            }
            if c == '"' {
                in_string = false;
            }
            current.push(c);
        } else if c == '"' {
            in_string = true;
            current.push(c);
        } else if c == '{' {
            depth += 1;
            current.push(c);
        } else if c == '}' {
            depth = depth.saturating_sub(1);
            current.push(c);
        } else if c == delim && depth == 0 {
            parts.push(current.trim().to_string());
            current = String::new();
        } else {
            current.push(c);
        }
        i += 1;
    }
    if !current.trim().is_empty() {
        parts.push(current.trim().to_string());
    }
    parts
}

pub fn parse_constant_value(s: &str) -> Option<Value> {
    let s = s.trim();
    if let Ok(n) = s.parse::<i64>() {
        return Some(Value::Int(n));
    }
    if s == "TRUE" {
        return Some(Value::Bool(true));
    }
    if s == "FALSE" {
        return Some(Value::Bool(false));
    }
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        let inner: Arc<str> = s[1..s.len() - 1].into();
        return Some(Value::Str(inner));
    }
    if s.starts_with('{') && s.ends_with('}') {
        let inner = s[1..s.len() - 1].trim();
        if inner.is_empty() {
            return Some(Value::Set(BTreeSet::new()));
        }
        let mut set = BTreeSet::new();
        for part in split_top_level(inner, ',') {
            if let Some(val) = parse_constant_value(&part) {
                set.insert(val);
            } else {
                return None;
            }
        }
        return Some(Value::Set(set));
    }
    if !s.is_empty() && s.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return Some(Value::Str(s.into()));
    }
    None
}

pub fn parse_cfg(input: &str) -> Result<TlcConfig, String> {
    let tokens = tokenize(input)?;
    let mut cfg = TlcConfig::new();
    let mut pos = 0;

    while pos < tokens.len() {
        match &tokens[pos] {
            Token::Keyword(kw) => match kw.as_str() {
                "INIT" => {
                    pos += 1;
                    let name = expect_ident(&tokens, &mut pos)?;
                    cfg.init = Some(Arc::from(name.as_str()));
                }
                "NEXT" => {
                    pos += 1;
                    let name = expect_ident(&tokens, &mut pos)?;
                    cfg.next = Some(Arc::from(name.as_str()));
                }
                "SPECIFICATION" => {
                    pos += 1;
                    let name = expect_ident(&tokens, &mut pos)?;
                    cfg.specification = Some(Arc::from(name.as_str()));
                }
                "CONSTANT" | "CONSTANTS" => {
                    pos += 1;
                    while pos < tokens.len() && !is_keyword(&tokens[pos]) {
                        let name = expect_ident(&tokens, &mut pos)?;
                        if pos < tokens.len() && tokens[pos] == Token::Eq {
                            pos += 1;
                            let val = parse_constant_value_from_tokens(&tokens, &mut pos)?;
                            cfg.constants.push((Arc::from(name.as_str()), val));
                        } else {
                            cfg.constants.push((
                                Arc::from(name.as_str()),
                                Value::Str(Arc::from(name.as_str())),
                            ));
                        }
                    }
                }
                "INVARIANT" | "INVARIANTS" => {
                    pos += 1;
                    while pos < tokens.len() && !is_keyword(&tokens[pos]) {
                        let name = expect_ident(&tokens, &mut pos)?;
                        cfg.invariants.push(Arc::from(name.as_str()));
                    }
                }
                "PROPERTY" | "PROPERTIES" => {
                    pos += 1;
                    while pos < tokens.len() && !is_keyword(&tokens[pos]) {
                        let name = expect_ident(&tokens, &mut pos)?;
                        cfg.properties.push(Arc::from(name.as_str()));
                    }
                }
                "SYMMETRY" => {
                    pos += 1;
                    let name = expect_ident(&tokens, &mut pos)?;
                    cfg.symmetry = Some(Arc::from(name.as_str()));
                }
                "CHECK_DEADLOCK" => {
                    pos += 1;
                    let name = expect_ident(&tokens, &mut pos)?;
                    match name.as_str() {
                        "TRUE" => cfg.check_deadlock = Some(true),
                        "FALSE" => cfg.check_deadlock = Some(false),
                        other => {
                            return Err(format!(
                                "CHECK_DEADLOCK expects TRUE or FALSE, got '{}'",
                                other
                            ));
                        }
                    }
                }
                "CONSTRAINT" | "CONSTRAINTS" => {
                    pos += 1;
                    while pos < tokens.len() && !is_keyword(&tokens[pos]) {
                        let name = expect_ident(&tokens, &mut pos)?;
                        cfg.constraints.push(Arc::from(name.as_str()));
                    }
                }
                "ACTION_CONSTRAINT" | "ACTION_CONSTRAINTS" => {
                    pos += 1;
                    while pos < tokens.len() && !is_keyword(&tokens[pos]) {
                        let name = expect_ident(&tokens, &mut pos)?;
                        cfg.action_constraints.push(Arc::from(name.as_str()));
                    }
                }
                other => return Err(format!("unknown directive: {}", other)),
            },
            other => return Err(format!("expected directive keyword, got {:?}", other)),
        }
    }

    if cfg.specification.is_some() && (cfg.init.is_some() || cfg.next.is_some()) {
        return Err("SPECIFICATION and INIT/NEXT are mutually exclusive in cfg file".to_string());
    }

    Ok(cfg)
}

fn expect_ident(tokens: &[Token], pos: &mut usize) -> Result<String, String> {
    if *pos >= tokens.len() {
        return Err("expected identifier, got end of input".to_string());
    }
    match &tokens[*pos] {
        Token::Ident(s) => {
            let name = s.clone();
            *pos += 1;
            Ok(name)
        }
        other => Err(format!("expected identifier, got {:?}", other)),
    }
}

pub fn apply_config(
    cfg: &TlcConfig,
    spec: &mut Spec,
    domains: &mut Env,
    checker_config: &mut CheckerConfig,
    cli_constants: &[(Arc<str>, Value)],
    cli_symmetry: &[Arc<str>],
    cli_allow_deadlock: bool,
) -> Result<Vec<String>, String> {
    let mut warnings = Vec::new();

    let mut seen_constants: Vec<&Arc<str>> = Vec::new();
    for (name, val) in &cfg.constants {
        if seen_constants.iter().any(|n| **n == *name) {
            warnings.push(format!(
                "duplicate CONSTANT '{}' in cfg file (last value wins)",
                name
            ));
        } else {
            seen_constants.push(name);
        }
        if cli_constants.iter().any(|(n, _)| n == name) {
            continue;
        }
        domains.insert(name.clone(), val.clone());
    }

    if let Some(ref init_name) = cfg.init {
        match spec.definitions.get(init_name.as_ref()) {
            Some((params, expr)) if params.is_empty() => {
                spec.init = Some(expr.clone());
            }
            Some(_) => {
                return Err(format!(
                    "INIT definition '{}' must have zero parameters",
                    init_name
                ));
            }
            None => {
                return Err(format!("INIT definition '{}' not found in spec", init_name));
            }
        }
    }

    if let Some(ref next_name) = cfg.next {
        match spec.definitions.get(next_name.as_ref()) {
            Some((params, expr)) if params.is_empty() => {
                spec.next = Some(expr.clone());
            }
            Some(_) => {
                return Err(format!(
                    "NEXT definition '{}' must have zero parameters",
                    next_name
                ));
            }
            None => {
                return Err(format!("NEXT definition '{}' not found in spec", next_name));
            }
        }
    }

    if let Some(ref spec_name) = cfg.specification {
        resolve_specification(spec_name, spec)?;
    }

    if !cfg.invariants.is_empty() {
        let mut new_invariants = Vec::new();
        let mut new_names = Vec::new();
        for inv_name in &cfg.invariants {
            match spec.definitions.get(inv_name.as_ref()) {
                Some((params, expr)) if params.is_empty() => {
                    new_invariants.push(expr.clone());
                    new_names.push(Some(inv_name.clone()));
                }
                Some(_) => {
                    return Err(format!(
                        "INVARIANT definition '{}' must have zero parameters",
                        inv_name
                    ));
                }
                None => {
                    return Err(format!(
                        "INVARIANT definition '{}' not found in spec",
                        inv_name
                    ));
                }
            }
        }
        spec.invariants = new_invariants;
        spec.invariant_names = new_names;
    }

    if !cfg.properties.is_empty() {
        for prop_name in &cfg.properties {
            match spec.definitions.get(prop_name.as_ref()) {
                Some((params, expr)) if params.is_empty() => {
                    spec.liveness_properties.push(expr.clone());
                }
                Some(_) => {
                    return Err(format!(
                        "PROPERTY definition '{}' must have zero parameters",
                        prop_name
                    ));
                }
                None => {
                    return Err(format!(
                        "PROPERTY definition '{}' not found in spec",
                        prop_name
                    ));
                }
            }
        }
        checker_config.check_liveness = true;
    }

    if let Some(ref sym_name) = cfg.symmetry
        && cli_symmetry.is_empty()
    {
        if let Some((_params, expr)) = spec.definitions.get(sym_name.as_ref()) {
            if let Expr::FnCall(const_name, _) = expr {
                checker_config.symmetric_constants.push(const_name.clone());
            } else if let Expr::Permutations(inner) = expr {
                if let Expr::Var(const_name) = inner.as_ref() {
                    checker_config.symmetric_constants.push(const_name.clone());
                } else {
                    checker_config.symmetric_constants.push(sym_name.clone());
                }
            } else if let Expr::Var(const_name) = expr {
                checker_config.symmetric_constants.push(const_name.clone());
            } else {
                checker_config.symmetric_constants.push(sym_name.clone());
            }
        } else {
            checker_config.symmetric_constants.push(sym_name.clone());
        }
    }

    if let Some(check_dl) = cfg.check_deadlock
        && !cli_allow_deadlock
    {
        checker_config.allow_deadlock = !check_dl;
    }

    if !cfg.constraints.is_empty() {
        for c in &cfg.constraints {
            warnings.push(format!("CONSTRAINT '{}' is not yet supported, ignoring", c));
        }
    }

    if !cfg.action_constraints.is_empty() {
        for c in &cfg.action_constraints {
            warnings.push(format!(
                "ACTION_CONSTRAINT '{}' is not yet supported, ignoring",
                c
            ));
        }
    }

    Ok(warnings)
}

fn find_box_action(expr: &Expr) -> Option<Expr> {
    match expr {
        Expr::BoxAction(next, _) => Some(*next.clone()),
        Expr::And(l, r) => find_box_action(l).or_else(|| find_box_action(r)),
        _ => None,
    }
}

fn leftmost_conjunct(expr: &Expr) -> &Expr {
    match expr {
        Expr::And(l, _) => leftmost_conjunct(l),
        other => other,
    }
}

fn resolve_specification(spec_name: &Arc<str>, spec: &mut Spec) -> Result<(), String> {
    match spec.definitions.get(spec_name.as_ref()) {
        Some((params, expr)) if params.is_empty() => {
            if let Some(next_expr) = find_box_action(expr) {
                spec.init = Some(leftmost_conjunct(expr).clone());
                spec.next = Some(next_expr);
                return Ok(());
            }
            Err(format!(
                "SPECIFICATION '{}': expected Init /\\ [][Next]_vars form",
                spec_name
            ))
        }
        Some(_) => Err(format!(
            "SPECIFICATION definition '{}' must have zero parameters",
            spec_name
        )),
        None => Err(format!(
            "SPECIFICATION definition '{}' not found in spec",
            spec_name
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_init_next() {
        let input = "INIT Init\nNEXT Next";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.init.as_deref(), Some("Init"));
        assert_eq!(cfg.next.as_deref(), Some("Next"));
    }

    #[test]
    fn parse_specification() {
        let input = "SPECIFICATION Spec";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.specification.as_deref(), Some("Spec"));
    }

    #[test]
    fn parse_specification_with_init_next_errors() {
        let input = "SPECIFICATION Spec\nINIT Init";
        let result = parse_cfg(input);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("mutually exclusive"));
    }

    #[test]
    fn parse_constants() {
        let input = "CONSTANT\nRM = {rm1, rm2, rm3}\nN = 5\nFlag = TRUE";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.constants.len(), 3);
        assert_eq!(cfg.constants[0].0.as_ref(), "RM");
        let mut expected_set = BTreeSet::new();
        expected_set.insert(Value::Str("rm1".into()));
        expected_set.insert(Value::Str("rm2".into()));
        expected_set.insert(Value::Str("rm3".into()));
        assert_eq!(cfg.constants[0].1, Value::Set(expected_set));
        assert_eq!(cfg.constants[1].1, Value::Int(5));
        assert_eq!(cfg.constants[2].1, Value::Bool(true));
    }

    #[test]
    fn parse_constant_string_values() {
        let input = "CONSTANT\nName = \"hello\"";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.constants[0].1, Value::Str("hello".into()));
    }

    #[test]
    fn parse_constant_empty_set() {
        let input = "CONSTANT\nS = {}";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.constants[0].1, Value::Set(BTreeSet::new()));
    }

    #[test]
    fn parse_constant_model_value() {
        let input = "CONSTANT\nX = ModelVal";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.constants[0].1, Value::Str("ModelVal".into()));
    }

    #[test]
    fn parse_constant_no_assignment() {
        let input = "CONSTANT\nX";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.constants[0].0.as_ref(), "X");
        assert_eq!(cfg.constants[0].1, Value::Str("X".into()));
    }

    #[test]
    fn parse_invariants() {
        let input = "INVARIANT TypeOK\nInvSafety";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.invariants.len(), 2);
        assert_eq!(cfg.invariants[0].as_ref(), "TypeOK");
        assert_eq!(cfg.invariants[1].as_ref(), "InvSafety");
    }

    #[test]
    fn parse_invariants_keyword() {
        let input = "INVARIANTS\nTypeOK\nInvSafety";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.invariants.len(), 2);
    }

    #[test]
    fn parse_properties() {
        let input = "PROPERTY Liveness";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.properties.len(), 1);
        assert_eq!(cfg.properties[0].as_ref(), "Liveness");
    }

    #[test]
    fn parse_symmetry() {
        let input = "SYMMETRY Perms";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.symmetry.as_deref(), Some("Perms"));
    }

    #[test]
    fn parse_check_deadlock_true() {
        let input = "CHECK_DEADLOCK TRUE";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.check_deadlock, Some(true));
    }

    #[test]
    fn parse_check_deadlock_false() {
        let input = "CHECK_DEADLOCK FALSE";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.check_deadlock, Some(false));
    }

    #[test]
    fn parse_constraints() {
        let input = "CONSTRAINT BoundedState";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.constraints.len(), 1);
        assert_eq!(cfg.constraints[0].as_ref(), "BoundedState");
    }

    #[test]
    fn parse_action_constraints() {
        let input = "ACTION_CONSTRAINT FairAction";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.action_constraints.len(), 1);
        assert_eq!(cfg.action_constraints[0].as_ref(), "FairAction");
    }

    #[test]
    fn parse_line_comment() {
        let input = "\\* this is a comment\nINIT Init\n\\* another comment\nNEXT Next";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.init.as_deref(), Some("Init"));
        assert_eq!(cfg.next.as_deref(), Some("Next"));
    }

    #[test]
    fn parse_block_comment() {
        let input = "(* block comment *)\nINIT Init\nNEXT Next";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.init.as_deref(), Some("Init"));
        assert_eq!(cfg.next.as_deref(), Some("Next"));
    }

    #[test]
    fn parse_full_cfg() {
        let input = r#"
            \* TwoPhase model configuration
            CONSTANT
                RM = {rm1, rm2, rm3}
            INIT TPInit
            NEXT TPNext
            INVARIANT TPTypeOK
            CHECK_DEADLOCK TRUE
        "#;
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.init.as_deref(), Some("TPInit"));
        assert_eq!(cfg.next.as_deref(), Some("TPNext"));
        assert_eq!(cfg.invariants.len(), 1);
        assert_eq!(cfg.invariants[0].as_ref(), "TPTypeOK");
        assert_eq!(cfg.check_deadlock, Some(true));
        assert_eq!(cfg.constants.len(), 1);
    }

    #[test]
    fn parse_negative_integer() {
        let input = "CONSTANT\nN = -3";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.constants[0].1, Value::Int(-3));
    }

    #[test]
    fn error_invalid_check_deadlock() {
        let input = "CHECK_DEADLOCK MAYBE";
        let result = parse_cfg(input);
        assert!(result.is_err());
    }

    #[test]
    fn error_unexpected_token() {
        let input = "= = =";
        let result = parse_cfg(input);
        assert!(result.is_err());
    }

    #[test]
    fn parse_constant_value_integers() {
        assert_eq!(parse_constant_value("42"), Some(Value::Int(42)));
        assert_eq!(parse_constant_value("-5"), Some(Value::Int(-5)));
        assert_eq!(parse_constant_value("0"), Some(Value::Int(0)));
    }

    #[test]
    fn parse_constant_value_booleans() {
        assert_eq!(parse_constant_value("TRUE"), Some(Value::Bool(true)));
        assert_eq!(parse_constant_value("FALSE"), Some(Value::Bool(false)));
    }

    #[test]
    fn parse_constant_value_strings() {
        assert_eq!(
            parse_constant_value("\"hello\""),
            Some(Value::Str("hello".into()))
        );
    }

    #[test]
    fn parse_constant_value_sets() {
        let mut expected = BTreeSet::new();
        expected.insert(Value::Str("a".into()));
        expected.insert(Value::Str("b".into()));
        assert_eq!(parse_constant_value("{a,b}"), Some(Value::Set(expected)));
    }

    #[test]
    fn parse_constant_value_model_value() {
        assert_eq!(
            parse_constant_value("myVal"),
            Some(Value::Str("myVal".into()))
        );
    }

    #[test]
    fn parse_multiple_constants_sections() {
        let input = "CONSTANT\nA = 1\nCONSTANT\nB = 2";
        let cfg = parse_cfg(input).unwrap();
        assert_eq!(cfg.constants.len(), 2);
        assert_eq!(cfg.constants[0].0.as_ref(), "A");
        assert_eq!(cfg.constants[1].0.as_ref(), "B");
    }

    #[test]
    fn parse_set_of_strings() {
        let input = r#"CONSTANT S = {"a", "b", "c"}"#;
        let cfg = parse_cfg(input).unwrap();
        let mut expected = BTreeSet::new();
        expected.insert(Value::Str("a".into()));
        expected.insert(Value::Str("b".into()));
        expected.insert(Value::Str("c".into()));
        assert_eq!(cfg.constants[0].1, Value::Set(expected));
    }

    #[test]
    fn parse_escaped_quotes_in_string() {
        let input = r#"CONSTANT S = {"hello\"world", "ok"}"#;
        let cfg = parse_cfg(input).unwrap();
        let mut expected = BTreeSet::new();
        expected.insert(Value::Str(r#"hello\"world"#.into()));
        expected.insert(Value::Str("ok".into()));
        assert_eq!(cfg.constants[0].1, Value::Set(expected));
    }

    #[test]
    fn split_top_level_escaped_quotes() {
        let result = split_top_level(r#""hello\"world","ok""#, ',');
        assert_eq!(result, vec![r#""hello\"world""#, r#""ok""#]);
    }

    #[test]
    fn apply_config_symmetry_permutations() {
        let mut spec = Spec {
            vars: vec![],
            init: None,
            next: None,
            invariants: vec![],
            invariant_names: vec![],
            definitions: std::collections::BTreeMap::new(),
            instances: vec![],
            extends: vec![],
            fairness: vec![],
            assumes: vec![],
            liveness_properties: vec![],
            constants: vec![],
        };
        spec.definitions.insert(
            Arc::from("Perms"),
            (
                vec![],
                Expr::Permutations(Box::new(Expr::Var(Arc::from("RM")))),
            ),
        );

        let cfg = parse_cfg("SYMMETRY Perms").unwrap();
        let mut domains = Env::new();
        let mut checker_config = CheckerConfig::default();

        apply_config(
            &cfg,
            &mut spec,
            &mut domains,
            &mut checker_config,
            &[],
            &[],
            false,
        )
        .unwrap();

        assert_eq!(checker_config.symmetric_constants, vec![Arc::from("RM")]);
    }
}
