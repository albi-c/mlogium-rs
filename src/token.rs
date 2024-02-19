use crate::position::Position;

pub enum TokenType {
    Id,

    KwLet,
    KwConst,
    KwFn,
    KwReturn,
    KwIf,
    KwElse,
    KwWhile,
    KwFor,
    KwBreak,
    KwContinue,
    KwIn,
    KwStruct,
    KwEnum,
    KwStatic,

    String,
    Number,

    Operator,
    Assignment,

    Arrow,
    Semicolon,
    Colon,
    DoubleColon,
    Dot,
    DoubleDot,
    Comma,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBrack,
    RBrack,
}

pub struct Token {
    type_: TokenType,
    text: String,
    position: Position,
}

impl Token {
    pub fn new(type_: TokenType, text: String, position: Position) -> Self {
        Token { type_, text, position }
    }
}
