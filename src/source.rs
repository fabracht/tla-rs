use std::sync::Arc;

use crate::span::Span;

#[derive(Clone)]
pub struct Source {
    text: Arc<str>,
    name: Arc<str>,
    line_starts: Vec<u32>,
}

impl Source {
    pub fn new(name: impl Into<Arc<str>>, text: impl Into<Arc<str>>) -> Self {
        let text: Arc<str> = text.into();
        let line_starts = compute_line_starts(&text);
        Self {
            text,
            name: name.into(),
            line_starts,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn line_col(&self, offset: u32) -> (usize, usize) {
        let offset = offset as usize;
        let line = self
            .line_starts
            .partition_point(|&start| (start as usize) <= offset)
            .saturating_sub(1);
        let line_start = self.line_starts.get(line).copied().unwrap_or(0) as usize;
        let col = offset.saturating_sub(line_start);
        (line + 1, col + 1)
    }

    pub fn line_text(&self, line: usize) -> &str {
        if line == 0 || line > self.line_starts.len() {
            return "";
        }
        let start = self.line_starts[line - 1] as usize;
        let end = self
            .line_starts
            .get(line)
            .map(|&e| e as usize)
            .unwrap_or(self.text.len());
        let text = &self.text[start..end];
        text.trim_end_matches('\n').trim_end_matches('\r')
    }

    pub fn line_count(&self) -> usize {
        self.line_starts.len()
    }

    pub fn slice(&self, span: Span) -> &str {
        let start = span.start as usize;
        let end = (span.end as usize).min(self.text.len());
        if start <= end && end <= self.text.len() {
            &self.text[start..end]
        } else {
            ""
        }
    }
}

fn compute_line_starts(text: &str) -> Vec<u32> {
    let mut starts = vec![0];
    for (i, c) in text.char_indices() {
        if c == '\n' {
            starts.push((i + 1) as u32);
        }
    }
    starts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_col_single_line() {
        let src = Source::new("test.tla", "x = 42");
        assert_eq!(src.line_col(0), (1, 1));
        assert_eq!(src.line_col(2), (1, 3));
        assert_eq!(src.line_col(5), (1, 6));
    }

    #[test]
    fn line_col_multi_line() {
        let src = Source::new("test.tla", "line1\nline2\nline3");
        assert_eq!(src.line_col(0), (1, 1));
        assert_eq!(src.line_col(5), (1, 6));
        assert_eq!(src.line_col(6), (2, 1));
        assert_eq!(src.line_col(12), (3, 1));
    }

    #[test]
    fn line_text_retrieval() {
        let src = Source::new("test.tla", "first\nsecond\nthird");
        assert_eq!(src.line_text(1), "first");
        assert_eq!(src.line_text(2), "second");
        assert_eq!(src.line_text(3), "third");
    }

    #[test]
    fn slice_extraction() {
        let src = Source::new("test.tla", "hello world");
        assert_eq!(src.slice(Span::new(0, 5)), "hello");
        assert_eq!(src.slice(Span::new(6, 11)), "world");
    }
}
