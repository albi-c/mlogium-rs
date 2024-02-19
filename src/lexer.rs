use std::error::Error;
use std::fmt::{Display, Formatter};
use std::ops::{Range, RangeBounds};
use crate::position::Position;
use crate::token::{Token, TokenType};

#[derive(Debug)]
pub struct Lexer<'a> {
    code: &'a str,
    code_vec: Vec<char>,
    code_lines: Vec<&'a str>,
    filename: &'a str,

    i: isize,
    line: isize,
    char: isize,
}

#[derive(Debug, Clone)]
pub struct LexerError {
    message: String,
    position: Position,
}

impl LexerError {
    pub fn new(message: &str, position: Position) -> Self {
        Self { message: message.into(), position }
    }
}

impl Display for LexerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl Error for LexerError {}

impl<'a> Lexer<'a> {
    pub fn new() -> Self {
        Self { code: "", code_vec: Vec::new(), code_lines: Vec::new(), filename: "", i: 0, line: 0, char: 0}
    }

    fn reset(&mut self, code: &'a str, filename: &'a str) {
        self.code = code;
        self.code_vec = self.code.chars().collect();
        self.code_lines = self.code.split('\n').collect();
        self.filename = filename;
        self.i = -1;
        self.line = 0;
        self.char = 0;
    }

    fn make_pos_n(&self, n: usize) -> Position {
        Position::new(self.line, self.char - n as isize, self.char - 1,
                      self.code_lines[self.line as usize], self.filename)
    }

    fn make_pos(&self) -> Position {
        self.make_pos_n(1)
    }

    fn has_n(&self, n: usize) -> bool {
        assert!(n >= 1);
        self.i < (self.code_vec.len() - n) as isize
    }

    fn has(&self) -> bool {
        self.has_n(1)
    }

    fn skip(&mut self) -> char {
        assert!(self.has());
        self.i += 1;
        self.char += 1;
        let ch = self.code_vec[self.i as usize];
        if ch == '\n' {
            self.line += 1;
            self.char = 0;
        }
        ch
    }

    fn next(&mut self) -> Result<char, LexerError> {
        if !self.has() {
            Err(LexerError::new("Unexpected EOF", self.make_pos()))
        } else {
            Ok(self.skip())
        }
    }

    fn next_expect(&mut self, expected: char) -> Result<char, LexerError> {
        let ch = self.next()?;
        if ch != expected {
            Err(LexerError::new(&*format!("Unexpected character: '{}', expected '{}'", ch, expected), self.make_pos()))
        } else {
            Ok(ch)
        }
    }

    fn current(&self) -> char {
        self.code_vec[self.i as usize]
    }

    fn lookahead_n(&self, n: usize) -> Option<char> {
        assert!(n >= 1);

        if !self.has_n(n) {
            None
        } else {
            Some(self.code_vec[self.i as usize + n])
        }
    }

    fn lookahead_no_take(&self) -> Option<char> {
        self.lookahead_n(1)
    }

    fn lookahead_n_expect_no_take(&self, n: usize, expected: char) -> bool {
        match self.lookahead_n(n) {
            Some(ch) => ch == expected,
            None => false
        }
    }

    fn lookahead_expect_no_take(&self, expected: char) -> bool {
        self.lookahead_n_expect_no_take(1, expected)
    }

    fn lookahead_n_expect_multi<R: RangeBounds<char>>(&self, n: usize, expected: R) -> Option<char> {
        match self.lookahead_n(n) {
            Some(ch) => if expected.contains(&ch) { Some(ch) } else { None },
            None => None
        }
    }

    fn lookahead_expect_multi<R: RangeBounds<char>>(&self, expected: R) -> Option<char> {
        match self.lookahead_no_take() {
            Some(ch) => if expected.contains(&ch) { Some(ch) } else { None },
            None => None
        }
    }

    fn lookahead_expect(&mut self, expected: char) -> bool {
        if self.lookahead_expect_no_take(expected) {
            self.skip();
            true
        } else {
            false
        }
    }

    fn lookahead_str(&mut self, expected: &str) -> bool {
        if !self.has_n(expected.len()) {
            false
        } else {
            self.code_vec[self.i as usize..self.i as usize + expected.len()].iter()
                .zip(expected.chars()).all(|(a, b)| *a == b)
        }
    }

    fn make_token(&self, type_: TokenType, text: &str) -> Token {
        Token::new(type_, text.into(), self.make_pos())
    }

    fn make_token_from_vec(&self, type_: TokenType, text: Vec<char>) -> Token {
        let text_str: String = text.into_iter().collect();
        Token::new(type_, text_str, self.make_pos())
    }

    fn lex_number(&mut self) -> Result<Token, LexerError> {
        let mut val = vec![self.next()?];

        while let Some(ch) = self.lookahead_expect_multi('0'..='9') {
            self.skip();
            val.push(ch);
        }

        if self.lookahead_expect_no_take('.') {
            if let Some(ch) = self.lookahead_n_expect_multi(2, '0'..='9') {
                self.skip();
                self.skip();
                val.push(ch);
                while let Some(ch) = self.lookahead_expect_multi('0'..='9') {
                    self.skip();
                    val.push(ch);
                }
            }
        }

        Ok(self.make_token_from_vec(TokenType::Number, val))
    }

    fn lex_string(&mut self) -> Result<Token, LexerError> {
        self.skip();

        let mut val = Vec::new();
        let mut prev = '\0';
        loop {
            let ch = self.next()?;
            if ch == '"' && prev != '\\' {
                break;
            }
            val.push(ch);
            prev = ch;
        }

        Ok(self.make_token_from_vec(TokenType::String, val))
    }

    fn lex_id(&mut self) -> Result<Token, LexerError> {
        let mut val = vec![self.next()?];

        Ok(self.make_token_from_vec(TokenType::Id, val))
    }

    fn lex_match(&mut self, ch: char) -> Option<Result<Token, LexerError>> {
        match ch {
            '0'..='9' => Some(self.lex_number()),
            '"' => Some(self.lex_string()),
            _ => None
        }
    }

    fn next_token(&mut self) -> Result<Option<Token>, LexerError> {
        let ch = self.lookahead_no_take().unwrap();

        if ch.is_whitespace() {
            self.skip();
            Ok(None)
        } else if self.lookahead_str("//") {
            while self.has() && self.next()? != '\n' {}
            Ok(None)
        } else if self.lookahead_str("->") {
            Ok(Some(self.make_token(TokenType::Arrow, "->")))
        } else if let Some(tok) = self.lex_match(ch) {
            Ok(Some(tok?))
        } else {
            Err(LexerError::new(&*format!("Unexpected character: '{}'", ch), self.make_pos()))
        }
    }

    pub fn lex(&mut self, code: &'a str, filename: &'a str) -> Result<Vec<Token>, LexerError> {
        self.reset(code, filename);

        let mut tokens = Vec::new();

        while self.has() {
            match self.next_token()? {
                Some(tok) => tokens.push(tok),
                None => {}
            };
        }

        Ok(tokens)
    }
}
