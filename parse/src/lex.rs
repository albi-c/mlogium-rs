use std::cell::RefCell;
use std::error::Error;
use std::fmt::Display;
use std::iter::Peekable;
use std::str::CharIndices;
use ariadne::Report;
use derive::ConvertKeywords;
use crate::error::{failure, hint_msg};
use crate::span::{Span, Spannable, Spanned};

#[derive(Debug, Copy, Clone, Eq, PartialEq, ConvertKeywords)]
pub enum TokType {
    #[kw_from]
    Id,

    #[kw = "_"]
    Underscore,

    LitString, LitInteger, LitFloat, LitChar,

    KwLet, KwConst, KwFn, KwReturn, KwIf, KwElse, KwWhile, KwFor, KwBreak, KwContinue, KwType,
    KwIn, KwStruct, KwEnum, KwStatic, KwAs, KwNamespace, KwMatch, KwSelf,

    Assign,
    Operator,
    Walrus,

    Arrow,
    FatArrow,

    Semicolon,
    Colon, DoubleColon,
    Dot, DoubleDot, Ellipsis,
    Comma,
    Hash,
    Question,
    Dollar,
    Exclamation,

    LParen, RParen,
    LBrace, RBrace,
    LBrack, RBrack,
}

impl TokType {
    pub fn name(self) -> &'static str {
        match self {
            TokType::Id => "identifier",
            TokType::Underscore => "'_'",

            TokType::LitString => "string literal",
            TokType::LitInteger => "integer literal",
            TokType::LitFloat => "float literal",
            TokType::LitChar => "character literal",

            TokType::KwLet => "'let'",
            TokType::KwConst => "'const'",
            TokType::KwFn => "'fn'",
            TokType::KwReturn => "'return'",
            TokType::KwIf => "'if'",
            TokType::KwElse => "'else'",
            TokType::KwWhile => "'while'",
            TokType::KwFor => "'for'",
            TokType::KwBreak => "'break'",
            TokType::KwContinue => "'continue'",
            TokType::KwType => "'type'",
            TokType::KwIn => "'in'",
            TokType::KwStruct => "'struct'",
            TokType::KwEnum => "'enum'",
            TokType::KwStatic => "'static'",
            TokType::KwAs => "'as'",
            TokType::KwNamespace => "'namespace'",
            TokType::KwMatch => "'match'",
            TokType::KwSelf => "'self'",

            TokType::Assign => "'='",
            TokType::Operator => "operator",
            TokType::Walrus => "':='",
            TokType::Arrow => "'->'",
            TokType::FatArrow => "'=>'",
            TokType::Semicolon => "';'",
            TokType::Colon => "':'",
            TokType::DoubleColon => "'::'",
            TokType::Dot => "'.'",
            TokType::DoubleDot => "'..'",
            TokType::Ellipsis => "'...'",
            TokType::Comma => "','",
            TokType::Hash => "'#'",
            TokType::Question => "'?'",
            TokType::Dollar => "'$'",
            TokType::Exclamation => "'!'",

            TokType::LParen => "'('",
            TokType::RParen => "')'",
            TokType::LBrace => "'{'",
            TokType::RBrace => "'}'",
            TokType::LBrack => "'['",
            TokType::RBrack => "']'",
        }
    }
}

macro_rules! tok_type {
    [=] => { TokType::Assign };
    [:=] => { TokType::Walrus };
    [->] => { TokType::Arrow };
    [=>] => { TokType::FatArrow };
    [;] => { TokType::Semicolon };
    [:] => { TokType::Colon };
    [::] => { TokType::DoubleColon };
    [.] => { TokType::Dot };
    [..] => { TokType::DoubleDot };
    [...] => { TokType::Ellipsis };
    [,] => { TokType::Comma };
    [#] => { TokType::Hash };
    [?] => { TokType::Question };
    [$] => { TokType::Dollar };
    [!] => { TokType::Exclamation };
}

#[derive(Debug, Clone)]
pub struct Tok<'a> {
    pub span: Span,
    pub ty: TokType,
    pub value: &'a str,
}

impl<'a> Tok<'a> {
    fn convert_keywords(mut self) -> Tok<'a> {
        self.ty = self.ty.convert_keywords(self.value);
        self
    }

    pub fn as_spanned_str(&self) -> Spanned<&'a str> {
        self.value.spanned(self.span.clone())
    }
}

#[derive(Debug)]
pub struct Lexer<'a> {
    code: &'a str,
    chars: RefCell<Peekable<CharIndices<'a>>>,
}

#[derive(Debug)]
pub enum LexerError {
    UnexpectedCharWithHint(usize, char, Box<[String]>),
    UnexpectedEof,
}

impl LexerError {
    pub fn into_report(self, src: &str) -> Report<Span> {
        match self {
            LexerError::UnexpectedEof =>
                failure("Unexpected end of input".into(),
                        ("Expected a character".into(), src.len()..src.len()), []),
            LexerError::UnexpectedCharWithHint(pos, ch, hint) =>
                failure(format!("Unexpected character: '{}'", ch),
                        (hint_msg(&hint), pos..pos), []),
        }
    }
}

impl Display for LexerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LexerError::UnexpectedCharWithHint(pos, ch, _) => {
                write!(f, "Unexpected character '{}' at {}", ch, pos)
            }
            LexerError::UnexpectedEof => {
                write!(f, "Unexpected EOF")
            },
        }
    }
}

impl Error for LexerError {
    fn description(&self) -> &str {
        match self {
            LexerError::UnexpectedCharWithHint(_, _, _) => "unexpected character",
            LexerError::UnexpectedEof => "unexpected EOF",
        }
    }
}

pub type LexerResult<T> = Result<T, LexerError>;

impl<'a> Lexer<'a> {
    pub fn new(code: &'a str) -> Self {
        Lexer {
            code,
            chars: RefCell::new(code.char_indices().peekable()),
        }
    }

    fn unexpected_char_with_ch_ref_hint<'b>(i: usize, ch: char, expected: &[char]) -> LexerError {
        LexerError::UnexpectedCharWithHint(
            i, ch,expected.into_iter().map(|&ch| ch.into()).collect())
    }

    fn unexpected_char_with_hint(i: usize, ch: char, expected: &[&str]) -> LexerError {
        LexerError::UnexpectedCharWithHint(
            i, ch, expected.into_iter().map(|s| s.to_string()).collect())
    }

    fn next(&self) -> Option<(usize, char)> {
        self.chars.borrow_mut().next()
    }

    fn peek(&self) -> Option<(usize, char)> {
        self.chars.borrow_mut().peek().copied()
    }

    fn peek_check(&self, ch: char) -> Option<(usize, char)> {
        match self.peek() {
            Some((i, c)) => if c == ch {
                Some((i, c))
            } else {
                None
            },
            None => None,
        }
    }

    fn peek_take(&self, ch: char) -> Option<(usize, char)> {
        if let Some(c) = self.peek_check(ch) {
            self.next().unwrap();
            Some(c)
        } else {
            None
        }
    }

    fn peek_str(&self, string: &str, take: bool) -> bool {
        if string.len() == 0 {
            return true;
        }

        let mut chars = self.chars.borrow().clone();

        if string.chars().all(|ch| chars.next().map(|(_, c)| c) == Some(ch)) {
            if take {
                for _ in 0..string.len() {
                    self.next().unwrap();
                }
            }
            true
        } else {
            false
        }
    }

    fn next_req(&self) -> LexerResult<(usize, char)> {
        self.next().ok_or_else(|| LexerError::UnexpectedEof)
    }

    fn take_while(&self, func: impl Fn(char) -> bool) {
        loop {
            if let Some((_, ch)) = self.peek() {
                if func(ch) {
                    self.next();
                    continue;
                }
            }
            break;
        }
    }

    fn make_tok(&self, start: usize, ty: TokType) -> Tok<'a> {
        let end = self.chars.borrow_mut().peek().unwrap().0;
        Tok {
            span: start..end,
            ty,
            value: &self.code[start..end],
        }
    }

    // pub fn lex_integer(&self) -> LexerResult<Option<Tok>> {
    //     if let Some((start, _)) = self.peek() {
    //         self.take_while(|ch| matches!(ch, '0'..='9'));
    //         Ok(Some(self.make_tok(start, TokType::LitInteger)))
    //     } else {
    //         Ok(None)
    //     }
    // }

    fn match_ident(ch: char) -> bool {
        matches!(ch, '0'..='9' | 'A'..='Z' | 'a'..='z' | '_')
    }

    fn lex_string(&self, start: usize, tok_type: TokType, end: char) -> LexerResult<Tok> {
        loop {
            let (_, ch) = self.next_req()?;

            if ch == '\\' {
                let (i, c) = self.next_req()?;
                const OPTIONS: &'static [char] =
                    &['n', 'r', 't', 'b', 'f', 'u', 'U', 'v', 'x', '0', '\\', '\"', '\''];
                if !OPTIONS.contains(&c) {
                    return Err(Self::unexpected_char_with_ch_ref_hint(i, c, OPTIONS));
                }
            } else if ch == end {
                break;
            }
        }
        Ok(self.make_tok(start, tok_type))
    }

    pub fn lex(&self) -> LexerResult<Option<Tok>> {
        while let Some((start, ch)) = self.next() {
            if ch.is_ascii_whitespace() {
                continue;
            }

            if self.peek_str("//", true) {
                self.take_while(|ch| ch != '\n');
                continue;
            }

            return Ok(Some(match ch {
                '0'..='9' => {
                    self.take_while(|ch| matches!(ch, '0'..='9'));
                    if self.peek_check('.').is_some() {
                        self.next().unwrap();
                        self.take_while(|ch| matches!(ch, '0'..='9'));
                        self.make_tok(start, TokType::LitFloat)
                    } else {
                        self.make_tok(start, TokType::LitInteger)
                    }
                },

                'a'..='z' | 'A'..='Z' | '_' => {
                    self.take_while(Self::match_ident);
                    self.make_tok(start, TokType::Id).convert_keywords()
                },

                '"' => self.lex_string(start, TokType::LitString, '"')?,

                '\'' => self.lex_string(start, TokType::LitChar, '\"')?,

                '=' => if self.peek_take('>').is_some() {
                    self.make_tok(start, tok_type![=>])
                } else if self.peek_take('=').is_some() {
                    self.make_tok(start, TokType::Operator)
                } else {
                    self.make_tok(start, tok_type![=])
                },

                '.' => if self.peek_take('.').is_some() {
                    if self.peek_take('.').is_some() {
                        self.make_tok(start, tok_type![...])
                    } else {
                        self.make_tok(start, tok_type![..])
                    }
                } else {
                    self.make_tok(start, tok_type![.])
                },

                ':' => if self.peek_take(':').is_some() {
                    self.make_tok(start, tok_type![::])
                } else if self.peek_take('=').is_some() {
                    self.make_tok(start, tok_type![:=])
                } else {
                    self.make_tok(start, tok_type![:])
                },

                ';' => self.make_tok(start, tok_type![;]),
                ',' => self.make_tok(start, tok_type![,]),
                '#' => self.make_tok(start, tok_type![#]),
                '?' => self.make_tok(start, tok_type![?]),
                '$' => self.make_tok(start, tok_type![$]),

                '!' => if self.peek_take('=').is_some() {
                    self.make_tok(start, TokType::Operator)
                } else {
                    self.make_tok(start, tok_type![!])
                },

                '(' => self.make_tok(start, TokType::LParen),
                ')' => self.make_tok(start, TokType::RParen),
                '{' => self.make_tok(start, TokType::LBrace),
                '}' => self.make_tok(start, TokType::RBrace),
                '[' => self.make_tok(start, TokType::LBrack),
                ']' => self.make_tok(start, TokType::RBrack),

                '-' => if self.peek_take('>').is_some() {
                    self.make_tok(start, tok_type![->])
                } else {
                    self.make_tok(start, TokType::Operator)
                },

                '*' | '&' | '|' => {
                    self.peek_take(ch);
                    self.make_tok(start, TokType::Operator)
                },
                '<' | '>' => {
                    if !self.peek_take(ch).is_some() {
                        self.peek_take('=');
                    }
                    self.make_tok(start, TokType::Operator)
                },
                '+' | '/' | '^' | '~' | '%' => self.make_tok(start, TokType::Operator),

                _ => return Err(Self::unexpected_char_with_hint(
                    start, ch, &["digit", "letter", "operator", "\"", "'"])),
            }))
        }

        Ok(None)
    }
}

pub struct LexerIterator<'a> {
    lexer: Lexer<'a>,
    peek: RefCell<Option<Tok<'a>>>,
    last: RefCell<Option<Tok<'a>>>,
}

impl<'a> LexerIterator<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self {
            lexer,
            peek: RefCell::new(None),
            last: RefCell::new(None),
        }
    }

    pub fn lexer<'b>(&'b self) -> &'b Lexer<'a> {
        assert!(self.peek.borrow().is_none());
        &self.lexer
    }

    pub fn next(&'a self) -> Option<LexerResult<Tok<'a>>> {
        if let Some(tok) = self.peek.borrow_mut().take() {
            self.last.replace(Some(tok.clone()));
            Some(Ok(tok))
        } else {
            match self.lexer.lex() {
                Ok(Some(tok)) => {
                    self.last.replace(Some(tok.clone()));
                    Some(Ok(tok))
                },
                Ok(None) => None,
                Err(err) => Some(Err(err)),
            }
        }
    }

    pub fn peek(&'a self) -> Option<LexerResult<Tok<'a>>> {
        if self.peek.borrow().is_none() {
            match self.lexer.lex() {
                Ok(tok) => self.peek.replace(tok),
                Err(err) => return Some(Err(err)),
            };
        }

        Ok(self.peek.borrow().clone()).transpose()
    }

    pub fn last(&'a self) -> Option<Tok<'a>> {
        self.last.take()
    }
}
