use std::fmt::Write;

use crate::source::Source;
use crate::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub severity: Severity,
    pub message: String,
    pub span: Option<Span>,
    pub label: Option<String>,
    pub note: Option<String>,
    pub help: Option<String>,
}

impl Diagnostic {
    pub fn error(message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Error,
            message: message.into(),
            span: None,
            label: None,
            note: None,
            help: None,
        }
    }

    pub fn warning(message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Warning,
            message: message.into(),
            span: None,
            label: None,
            note: None,
            help: None,
        }
    }

    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.label = Some(label.into());
        self
    }

    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        let new_note = note.into();
        self.note = Some(match self.note {
            Some(existing) => format!("{}\n   = note: {}", existing, new_note),
            None => new_note,
        });
        self
    }

    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    pub fn render(&self, source: &Source) -> String {
        let mut out = String::new();
        self.render_to(&mut out, source);
        out
    }

    pub fn render_to(&self, out: &mut String, source: &Source) {
        let severity_str = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };

        let _ = writeln!(out, "{}: {}", severity_str, self.message);

        if let Some(span) = self.span {
            let (line, col) = source.line_col(span.start);
            let _ = writeln!(out, "  --> {}:{}:{}", source.name(), line, col);
            let _ = writeln!(out, "   |");

            let line_text = source.line_text(line);
            let line_num_width = line.to_string().len().max(2);

            if line > 1 {
                let ctx_text = source.line_text(line - 1);
                let _ = writeln!(
                    out,
                    "{:>width$} | {}",
                    line - 1,
                    ctx_text,
                    width = line_num_width
                );
            }

            let _ = writeln!(
                out,
                "{:>width$} | {}",
                line,
                line_text,
                width = line_num_width
            );

            let line_start = source.line_col(span.start).1;
            let span_len = span.len() as usize;
            let underline_len = span_len
                .max(1)
                .min(line_text.len().saturating_sub(line_start - 1));

            let _ = write!(
                out,
                "{:>width$} | {:padding$}",
                "",
                "",
                width = line_num_width,
                padding = line_start - 1
            );

            for _ in 0..underline_len {
                out.push('^');
            }

            if let Some(ref label) = self.label {
                let _ = write!(out, " {}", label);
            }
            out.push('\n');
        }

        if self.note.is_some() || self.help.is_some() {
            let _ = writeln!(out, "   |");
        }
        if let Some(ref note) = self.note {
            let _ = writeln!(out, "   = note: {}", note);
        }
        if let Some(ref help) = self.help {
            let _ = writeln!(out, "   = help: {}", help);
        }
    }

    pub fn render_simple(&self) -> String {
        let severity_str = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };
        let mut out = format!("{}: {}", severity_str, self.message);
        if let Some(ref note) = self.note {
            out.push_str(&format!("\nnote: {}", note));
        }
        if let Some(ref help) = self.help {
            out.push_str(&format!("\nhelp: {}", help));
        }
        out
    }
}

pub struct ColorConfig {
    enabled: bool,
}

impl ColorConfig {
    pub fn detect() -> Self {
        use std::io::IsTerminal;
        Self {
            enabled: std::env::var("NO_COLOR").is_err() && std::io::stderr().is_terminal(),
        }
    }

    pub fn disabled() -> Self {
        Self { enabled: false }
    }

    fn red_bold(&self, text: &str) -> String {
        if self.enabled {
            format!("\x1b[1;31m{}\x1b[0m", text)
        } else {
            text.to_string()
        }
    }

    fn yellow_bold(&self, text: &str) -> String {
        if self.enabled {
            format!("\x1b[1;33m{}\x1b[0m", text)
        } else {
            text.to_string()
        }
    }

    fn bold(&self, text: &str) -> String {
        if self.enabled {
            format!("\x1b[1m{}\x1b[0m", text)
        } else {
            text.to_string()
        }
    }

    fn blue(&self, text: &str) -> String {
        if self.enabled {
            format!("\x1b[34m{}\x1b[0m", text)
        } else {
            text.to_string()
        }
    }

    fn red(&self, text: &str) -> String {
        if self.enabled {
            format!("\x1b[31m{}\x1b[0m", text)
        } else {
            text.to_string()
        }
    }

    fn cyan(&self, text: &str) -> String {
        if self.enabled {
            format!("\x1b[36m{}\x1b[0m", text)
        } else {
            text.to_string()
        }
    }
}

impl Diagnostic {
    pub fn render_colored(&self, source: &Source, colors: &ColorConfig) -> String {
        let mut out = String::new();

        let severity_str = match self.severity {
            Severity::Error => colors.red_bold("error"),
            Severity::Warning => colors.yellow_bold("warning"),
        };
        let _ = writeln!(out, "{}: {}", severity_str, colors.bold(&self.message));

        if let Some(span) = self.span {
            let (line, col) = source.line_col(span.start);
            let _ = writeln!(
                out,
                "  {} {}:{}:{}",
                colors.blue("-->"),
                source.name(),
                line,
                col
            );
            let _ = writeln!(out, "   {}", colors.blue("|"));

            let line_text = source.line_text(line);
            let line_num_width = line.to_string().len().max(2);

            if line > 1 {
                let ctx_text = source.line_text(line - 1);
                let _ = writeln!(
                    out,
                    "{} {} {}",
                    colors.blue(&format!("{:>width$}", line - 1, width = line_num_width)),
                    colors.blue("|"),
                    ctx_text
                );
            }

            let _ = writeln!(
                out,
                "{} {} {}",
                colors.blue(&format!("{:>width$}", line, width = line_num_width)),
                colors.blue("|"),
                line_text
            );

            let line_start = source.line_col(span.start).1;
            let span_len = span.len() as usize;
            let underline_len = span_len
                .max(1)
                .min(line_text.len().saturating_sub(line_start - 1));

            let padding: String = std::iter::repeat_n(' ', line_start - 1).collect();
            let carets: String = std::iter::repeat_n('^', underline_len).collect();
            let label_str = self
                .label
                .as_ref()
                .map(|l| format!(" {}", l))
                .unwrap_or_default();

            let _ = writeln!(
                out,
                "{} {} {}{}",
                colors.blue(&format!("{:>width$}", "", width = line_num_width)),
                colors.blue("|"),
                padding,
                colors.red(&format!("{}{}", carets, label_str))
            );
        }

        if self.note.is_some() || self.help.is_some() {
            let _ = writeln!(out, "   {}", colors.blue("|"));
        }
        if let Some(ref note) = self.note {
            let _ = writeln!(out, "   {} {}", colors.blue("="), colors.cyan(&format!("note: {}", note)));
        }
        if let Some(ref help) = self.help {
            let _ = writeln!(out, "   {} {}", colors.blue("="), colors.cyan(&format!("help: {}", help)));
        }

        out
    }
}

pub fn levenshtein_distance(a: &str, b: &str) -> usize {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let a_len = a_chars.len();
    let b_len = b_chars.len();

    if a_len == 0 {
        return b_len;
    }
    if b_len == 0 {
        return a_len;
    }

    let mut prev_row: Vec<usize> = (0..=b_len).collect();
    let mut curr_row: Vec<usize> = vec![0; b_len + 1];

    for i in 1..=a_len {
        curr_row[0] = i;
        for j in 1..=b_len {
            let cost = if a_chars[i - 1] == b_chars[j - 1] {
                0
            } else {
                1
            };
            curr_row[j] = (prev_row[j] + 1)
                .min(curr_row[j - 1] + 1)
                .min(prev_row[j - 1] + cost);
        }
        std::mem::swap(&mut prev_row, &mut curr_row);
    }

    prev_row[b_len]
}

pub fn find_similar<'a>(
    name: &str,
    candidates: impl Iterator<Item = &'a str>,
    max_dist: usize,
) -> Option<&'a str> {
    let mut best: Option<(&str, usize)> = None;
    for candidate in candidates {
        let dist = levenshtein_distance(name, candidate);
        if dist <= max_dist {
            if let Some((_, best_dist)) = best {
                if dist < best_dist {
                    best = Some((candidate, dist));
                }
            } else {
                best = Some((candidate, dist));
            }
        }
    }
    best.map(|(s, _)| s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn render_error_with_span() {
        let src = Source::new("test.tla", "x = coutn + 1");
        let diag = Diagnostic::error("undefined variable `coutn`")
            .with_span(Span::new(4, 9))
            .with_label("not found")
            .with_help("did you mean `count`?");

        let output = diag.render(&src);
        assert!(output.contains("error: undefined variable `coutn`"));
        assert!(output.contains("test.tla:1:5"));
        assert!(output.contains("^^^^^"));
        assert!(output.contains("did you mean `count`"));
    }

    #[test]
    fn levenshtein_basic() {
        assert_eq!(levenshtein_distance("kitten", "sitting"), 3);
        assert_eq!(levenshtein_distance("", "abc"), 3);
        assert_eq!(levenshtein_distance("abc", "abc"), 0);
        assert_eq!(levenshtein_distance("coutn", "count"), 2);
    }

    #[test]
    fn find_similar_names() {
        let names = ["count", "counter", "total", "value"];
        let result = find_similar("coutn", names.iter().copied(), 2);
        assert_eq!(result, Some("count"));
    }
}
