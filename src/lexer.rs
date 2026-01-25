use std::sync::Arc;

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Ident(Arc<str>),
    Int(i64),
    Str(Arc<str>),
    True,
    False,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    LAngle,
    RAngle,
    Comma,
    Colon,
    Dot,
    Prime,
    Underscore,

    Eq,
    EqEq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Div,
    Mod,
    DotDot,
    MapsTo,
    ColonGt,
    AtAt,
    At,
    Bang,

    And,
    Or,
    Not,
    Implies,
    Equiv,
    Eventually,
    Always,
    LeadsTo,
    In,
    NotIn,
    Union,
    BigUnion,
    Intersect,
    SetMinus,
    Subseteq,
    ProperSubset,
    Supseteq,
    ProperSupset,
    Times,

    Module,
    Extends,
    Variables,
    Constants,
    Assume,
    Theorem,
    Invariant,
    If,
    Then,
    Else,
    Case,
    Other,
    Let,
    Def,
    Except,
    Domain,
    Subset,
    Cardinality,
    IsFiniteSet,
    Unchanged,
    Choose,
    Exists,
    Forall,
    Recursive,
    Lambda,
    Instance,
    Local,
    With,
    By,
    ProofDef,
    Qed,
    Lemma,
    Enabled,
    ProofStep,
    LabelSep,
    Semicolon,
    Dollar,
    Pipe,
    Caret,
    Ampersand,
    LeftArrow,
    RightArrow,
    Concat,
    Len,
    Head,
    Tail,
    Append,
    SubSeq,
    SelectSeq,
    Seq,
    Print,
    Assert,
    JavaTime,
    SystemTime,
    Permutations,
    SortSeq,
    PrintT,
    TLCToString,
    RandomElement,
    TLCGet,
    TLCSet,
    Any,
    TLCEval,
    IsABag,
    BagToSet,
    SetToBag,
    BagIn,
    EmptyBag,
    BagUnion,
    SubBag,
    BagOfAll,
    BagCardinality,
    CopiesIn,
    BagAdd,
    BagSub,
    SqSubseteq,
    CustomOp(Arc<str>),

    Eof,
}

pub struct Lexer<'a> {
    input: &'a str,
    pos: usize,
    seen_module: bool,
    module_ended: bool,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self { input, pos: 0, seen_module: false, module_ended: false }
    }

    fn peek_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.peek_char()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            while self.peek_char().is_some_and(|c| c.is_whitespace()) {
                self.advance();
            }
            if self.starts_with("\\*") {
                while self.peek_char().is_some_and(|c| c != '\n') {
                    self.advance();
                }
            } else if self.starts_with("(*") {
                self.advance();
                self.advance();
                while !self.starts_with("*)") && self.peek_char().is_some() {
                    self.advance();
                }
                if self.starts_with("*)") {
                    self.advance();
                    self.advance();
                }
            } else if self.at_line_start() && self.peek_char() == Some('-') {
                let start = self.pos;
                while self.peek_char() == Some('-') {
                    self.advance();
                }
                if self.pos - start >= 4 {
                    while self.peek_char().is_some_and(|c| c != '\n') {
                        self.advance();
                    }
                } else {
                    self.pos = start;
                    break;
                }
            } else if self.at_line_start() && self.peek_char() == Some('=') {
                let start = self.pos;
                while self.peek_char() == Some('=') {
                    self.advance();
                }
                if self.pos - start >= 4 {
                    if self.seen_module {
                        self.module_ended = true;
                        return;
                    }
                    while self.peek_char().is_some_and(|c| c != '\n') {
                        self.advance();
                    }
                } else {
                    self.pos = start;
                    break;
                }
            } else {
                break;
            }
        }
    }

    fn at_line_start(&self) -> bool {
        self.pos == 0 || self.input[..self.pos].ends_with('\n')
    }

    fn starts_with(&self, s: &str) -> bool {
        self.input[self.pos..].starts_with(s)
    }

    fn consume(&mut self, s: &str) -> bool {
        if self.starts_with(s) {
            self.pos += s.len();
            true
        } else {
            false
        }
    }

    pub fn next_token(&mut self) -> Result<Token, String> {
        self.skip_whitespace_and_comments();

        if self.module_ended || self.pos >= self.input.len() {
            return Ok(Token::Eof);
        }

        if self.consume("<=>") {
            return Ok(Token::Equiv);
        }
        if self.consume("<>") {
            return Ok(Token::Eventually);
        }
        if self.consume("[]") {
            return Ok(Token::Always);
        }
        if self.consume("~>") {
            return Ok(Token::LeadsTo);
        }
        if self.starts_with("<") && self.input[self.pos + 1..]
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_digit())
        {
            self.advance();
            while self.peek_char().is_some_and(|c| c.is_ascii_digit()) {
                self.advance();
            }
            if self.peek_char() == Some('>') {
                self.advance();
            }
            while self.peek_char().is_some_and(|c| c.is_alphanumeric() || c == '.') {
                self.advance();
            }
            return Ok(Token::ProofStep);
        }
        if self.consume("<<") {
            return Ok(Token::LAngle);
        }
        if self.consume(">>") {
            return Ok(Token::RAngle);
        }
        if self.consume("..") {
            return Ok(Token::DotDot);
        }
        if self.consume("|->") {
            return Ok(Token::MapsTo);
        }
        if self.consume("::") {
            return Ok(Token::LabelSep);
        }
        if self.consume(":>") {
            return Ok(Token::ColonGt);
        }
        if self.consume("@@") {
            return Ok(Token::AtAt);
        }
        if self.consume("@") {
            return Ok(Token::At);
        }
        if self.consume("==") {
            return Ok(Token::EqEq);
        }
        if self.consume("#") || self.consume("/=") || self.consume("\\#") || self.consume("≠") {
            return Ok(Token::Neq);
        }
        if self.consume("<=") || self.consume("=<") || self.consume("\\leq") || self.consume("≤") {
            return Ok(Token::Le);
        }
        if self.consume(">=") || self.consume("\\geq") || self.consume("≥") {
            return Ok(Token::Ge);
        }
        if self.consume("/\\") || self.consume("\\land") || self.consume("∧") {
            return Ok(Token::And);
        }
        if self.consume("\\/") || self.consume("\\lor") || self.consume("∨") {
            return Ok(Token::Or);
        }
        if self.consume("=>") || self.consume("⟹") || self.consume("⇒") {
            return Ok(Token::Implies);
        }
        if self.consume("\\notin") || self.consume("∉") {
            return Ok(Token::NotIn);
        }
        if self.consume("\\in") || self.consume("∈") {
            return Ok(Token::In);
        }
        if self.consume("\\union") || self.consume("\\cup") || self.consume("∪") {
            return Ok(Token::Union);
        }
        if self.consume("\\intersect") || self.consume("\\cap") || self.consume("∩") {
            return Ok(Token::Intersect);
        }
        if self.consume("\\subseteq") || self.consume("⊆") {
            return Ok(Token::Subseteq);
        }
        if self.consume("\\subset") || self.consume("⊂") {
            return Ok(Token::ProperSubset);
        }
        if self.consume("\\supseteq") || self.consume("⊇") {
            return Ok(Token::Supseteq);
        }
        if self.consume("\\supset") || self.consume("⊃") {
            return Ok(Token::ProperSupset);
        }
        if self.consume("\\times") || self.consume("\\X") || self.consume("×") {
            return Ok(Token::Times);
        }
        if self.consume("\\oplus") || self.consume("(+)") || self.consume("⊕") {
            return Ok(Token::BagAdd);
        }
        if self.consume("\\ominus") || self.consume("(-)") || self.consume("⊖") {
            return Ok(Token::BagSub);
        }
        if self.consume("\\sqsubseteq") || self.consume("⊑") {
            return Ok(Token::SqSubseteq);
        }
        if self.consume("\\div") {
            return Ok(Token::Div);
        }
        if self.starts_with("\\b") {
            let rest = &self.input[self.pos + 2..];
            if let Some(c) = rest.chars().next()
                && (c == '0' || c == '1')
            {
                self.pos += 2;
                let start = self.pos;
                while self.peek_char().is_some_and(|c| c == '0' || c == '1') {
                    self.advance();
                }
                let n = i64::from_str_radix(&self.input[start..self.pos], 2)
                    .map_err(|_| "invalid binary integer")?;
                return Ok(Token::Int(n));
            }
        }
        if self.starts_with("\\o") {
            let rest = &self.input[self.pos + 2..];
            if let Some(c) = rest.chars().next()
                && c.is_ascii_digit()
                && c < '8'
            {
                self.pos += 2;
                let start = self.pos;
                while self.peek_char().is_some_and(|c| c.is_ascii_digit() && c < '8') {
                    self.advance();
                }
                let n = i64::from_str_radix(&self.input[start..self.pos], 8)
                    .map_err(|_| "invalid octal integer")?;
                return Ok(Token::Int(n));
            }
        }
        if self.starts_with("\\h") || self.starts_with("\\H") {
            let rest = &self.input[self.pos + 2..];
            if let Some(c) = rest.chars().next()
                && c.is_ascii_hexdigit()
            {
                self.pos += 2;
                let start = self.pos;
                while self.peek_char().is_some_and(|c| c.is_ascii_hexdigit()) {
                    self.advance();
                }
                let n = i64::from_str_radix(&self.input[start..self.pos], 16)
                    .map_err(|_| "invalid hexadecimal integer")?;
                return Ok(Token::Int(n));
            }
        }
        if self.consume("\\E") || self.consume("\\exists") || self.consume("∃") {
            return Ok(Token::Exists);
        }
        if self.consume("\\A") || self.consume("\\forall") || self.consume("∀") {
            return Ok(Token::Forall);
        }
        if self.consume("~") || self.consume("\\lnot") || self.consume("\\neg") || self.consume("¬") {
            return Ok(Token::Not);
        }
        if self.starts_with("\\o")
            && !self.input[self.pos + 2..]
                .chars()
                .next()
                .is_some_and(|c| c.is_alphanumeric())
        {
            self.pos += 2;
            return Ok(Token::Concat);
        }
        if self.starts_with("\\") && self.input[self.pos + 1..]
            .chars()
            .next()
            .is_some_and(|c| c.is_alphabetic())
        {
            self.advance();
            let start = self.pos;
            while self
                .peek_char()
                .is_some_and(|c| c.is_alphanumeric() || c == '_')
            {
                self.advance();
            }
            let name: Arc<str> = self.input[start..self.pos].into();
            return Ok(Token::CustomOp(name));
        }
        if self.consume("\\") {
            return Ok(Token::SetMinus);
        }
        if self.consume("<-") {
            return Ok(Token::LeftArrow);
        }
        if self.consume("->") {
            return Ok(Token::RightArrow);
        }

        let c = self.peek_char().unwrap();

        if c == '(' {
            self.advance();
            return Ok(Token::LParen);
        }
        if c == ')' {
            self.advance();
            return Ok(Token::RParen);
        }
        if c == '{' {
            self.advance();
            return Ok(Token::LBrace);
        }
        if c == '}' {
            self.advance();
            return Ok(Token::RBrace);
        }
        if c == '[' {
            self.advance();
            return Ok(Token::LBracket);
        }
        if c == ']' {
            self.advance();
            return Ok(Token::RBracket);
        }
        if c == ',' {
            self.advance();
            return Ok(Token::Comma);
        }
        if c == ':' {
            self.advance();
            return Ok(Token::Colon);
        }
        if c == '.' {
            self.advance();
            return Ok(Token::Dot);
        }
        if c == '\'' {
            self.advance();
            return Ok(Token::Prime);
        }
        if c == '_' {
            self.advance();
            return Ok(Token::Underscore);
        }
        if c == ';' {
            self.advance();
            return Ok(Token::Semicolon);
        }
        if c == '$' {
            self.advance();
            return Ok(Token::Dollar);
        }
        if c == '|' {
            self.advance();
            return Ok(Token::Pipe);
        }
        if c == '^' {
            self.advance();
            return Ok(Token::Caret);
        }
        if c == '&' {
            self.advance();
            return Ok(Token::Ampersand);
        }
        if c == '=' {
            self.advance();
            return Ok(Token::Eq);
        }
        if c == '<' {
            self.advance();
            return Ok(Token::Lt);
        }
        if c == '>' {
            self.advance();
            return Ok(Token::Gt);
        }
        if c == '+' {
            self.advance();
            return Ok(Token::Plus);
        }
        if c == '-' {
            self.advance();
            return Ok(Token::Minus);
        }
        if c == '*' {
            self.advance();
            return Ok(Token::Star);
        }
        if c == '%' {
            self.advance();
            return Ok(Token::Mod);
        }
        if c == '/' {
            self.advance();
            return Ok(Token::Div);
        }
        if c == '!' {
            self.advance();
            return Ok(Token::Bang);
        }

        if c == '"' {
            self.advance();
            let start = self.pos;
            while self.peek_char().is_some_and(|c| c != '"') {
                self.advance();
            }
            let s: Arc<str> = self.input[start..self.pos].into();
            self.advance();
            return Ok(Token::Str(s));
        }

        if c.is_ascii_digit() {
            let start = self.pos;
            while self.peek_char().is_some_and(|c| c.is_ascii_digit()) {
                self.advance();
            }
            let n: i64 = self.input[start..self.pos]
                .parse()
                .map_err(|_| "invalid integer")?;
            return Ok(Token::Int(n));
        }

        if c.is_alphabetic() || c == '_' {
            let start = self.pos;
            while self
                .peek_char()
                .is_some_and(|c| c.is_alphanumeric() || c == '_')
            {
                self.advance();
            }
            let ident = &self.input[start..self.pos];
            let tok = match ident {
                "TRUE" => Token::True,
                "FALSE" => Token::False,
                "MODULE" => {
                    self.seen_module = true;
                    Token::Module
                }
                "EXTENDS" => Token::Extends,
                "VARIABLES" | "VARIABLE" => Token::Variables,
                "CONSTANTS" | "CONSTANT" => Token::Constants,
                "ASSUME" | "ASSUMPTION" | "AXIOM" => Token::Assume,
                "THEOREM" => Token::Theorem,
                "Invariant" => Token::Invariant,
                "IF" => Token::If,
                "THEN" => Token::Then,
                "ELSE" => Token::Else,
                "CASE" => Token::Case,
                "OTHER" => Token::Other,
                "LET" => Token::Let,
                "IN" => Token::Def,
                "EXCEPT" => Token::Except,
                "DOMAIN" => Token::Domain,
                "SUBSET" => Token::Subset,
                "UNION" => Token::BigUnion,
                "Cardinality" => Token::Cardinality,
                "IsFiniteSet" => Token::IsFiniteSet,
                "UNCHANGED" => Token::Unchanged,
                "CHOOSE" => Token::Choose,
                "RECURSIVE" => Token::Recursive,
                "LAMBDA" => Token::Lambda,
                "INSTANCE" => Token::Instance,
                "LOCAL" => Token::Local,
                "WITH" => Token::With,
                "Len" => Token::Len,
                "Head" => Token::Head,
                "Tail" => Token::Tail,
                "Append" => Token::Append,
                "SubSeq" => Token::SubSeq,
                "SelectSeq" => Token::SelectSeq,
                "Seq" => Token::Seq,
                "Print" => Token::Print,
                "Assert" => Token::Assert,
                "JavaTime" => Token::JavaTime,
                "SystemTime" => Token::SystemTime,
                "Permutations" => Token::Permutations,
                "SortSeq" => Token::SortSeq,
                "PrintT" => Token::PrintT,
                "ToString" => Token::TLCToString,
                "RandomElement" => Token::RandomElement,
                "TLCGet" => Token::TLCGet,
                "TLCSet" => Token::TLCSet,
                "Any" => Token::Any,
                "TLCEval" => Token::TLCEval,
                "IsABag" => Token::IsABag,
                "BagToSet" => Token::BagToSet,
                "SetToBag" => Token::SetToBag,
                "BagIn" => Token::BagIn,
                "EmptyBag" => Token::EmptyBag,
                "BagUnion" => Token::BagUnion,
                "SubBag" => Token::SubBag,
                "BagOfAll" => Token::BagOfAll,
                "BagCardinality" => Token::BagCardinality,
                "CopiesIn" => Token::CopiesIn,
                "BY" => Token::By,
                "DEF" => Token::ProofDef,
                "QED" => Token::Qed,
                "LEMMA" => Token::Lemma,
                "ENABLED" => Token::Enabled,
                "DEFINE" => Token::Let,
                "PICK" => Token::Choose,
                "WITNESS" => Token::By,
                "OBVIOUS" => Token::By,
                "OMITTED" => Token::By,
                "NEW" => Token::By,
                "PROVE" => Token::By,
                "SUFFICES" => Token::By,
                "COROLLARY" => Token::Lemma,
                "HAVE" => Token::By,
                "TAKE" => Token::By,
                "USE" => Token::By,
                "HIDE" => Token::By,
                "DEFS" => Token::ProofDef,
                "ONLY" => Token::By,
                _ => Token::Ident(ident.into()),
            };
            return Ok(tok);
        }

        Err(format!("unexpected character: {}", c))
    }

    pub fn tokenize(&mut self) -> Result<Vec<Token>, String> {
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token()?;
            if tok == Token::Eof {
                tokens.push(tok);
                break;
            }
            tokens.push(tok);
        }
        Ok(tokens)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_basic() {
        let mut lexer = Lexer::new("x' = 1 /\\ y \\in {1, 2}");
        let tokens = lexer.tokenize().unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::Ident("x".into()),
                Token::Prime,
                Token::Eq,
                Token::Int(1),
                Token::And,
                Token::Ident("y".into()),
                Token::In,
                Token::LBrace,
                Token::Int(1),
                Token::Comma,
                Token::Int(2),
                Token::RBrace,
                Token::Eof,
            ]
        );
    }

    #[test]
    fn lex_operators() {
        let mut lexer = Lexer::new("<< >> .. |-> == <= >= => \\union \\E \\A");
        let tokens = lexer.tokenize().unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::LAngle,
                Token::RAngle,
                Token::DotDot,
                Token::MapsTo,
                Token::EqEq,
                Token::Le,
                Token::Ge,
                Token::Implies,
                Token::Union,
                Token::Exists,
                Token::Forall,
                Token::Eof,
            ]
        );
    }

    #[test]
    fn lex_comment() {
        let mut lexer = Lexer::new("x \\* comment\n y (* block *) z");
        let tokens = lexer.tokenize().unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::Ident("x".into()),
                Token::Ident("y".into()),
                Token::Ident("z".into()),
                Token::Eof,
            ]
        );
    }
}
