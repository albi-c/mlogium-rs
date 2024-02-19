use std::cmp::{max, min};

#[derive(Debug, Clone)]
pub struct Position {
    line: isize,
    start: isize,
    end: isize,
    code: String,
    file: String
}

impl Position {
    pub fn new(line: isize, start: isize, end: isize, code: &str, file: &str) -> Self {
        Position { line, start, end, code: code.into(), file: file.into() }
    }

    pub fn join(&self, other: &Self) -> Self {
        if self.line < other.line {
            Position::new(self.line, 0, self.end, &*self.code, &*self.file)
        } else if self.line > other.line {
            Position::new(other.line, 0, other.end, &*other.code, &*other.file)
        } else {
            Position::new(self.line, min(self.start, other.start), max(self.end, other.end),
                          &*self.code, &*self.file)
        }
    }
}
