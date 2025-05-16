use std::str::FromStr;
use ariadne::Report;
use crate::ast::{Ast, FunctionParam, LambdaCapture, LambdaParam, MatchPatAst, StructElement, StructMethodSelf, TypeAst, TypeConstraintAst, UnnamedFunctionParam};
use crate::error::{failure, hint_msg};
use crate::lex::{Lexer, LexerError, LexerIterator, Tok, TokType};
use crate::span::{spanned, spanned_ok, Span, Spannable, Spanned};

#[derive(Debug)]
pub enum ParserError {
    LexerError(LexerError),
    UnexpectedToken(Span, TokType, String, Box<[String]>),
    FloatParseError(Span, String, String),
    IntParseError(Span, String, String),
}

impl ParserError {
    fn unexpected<'a>(tok: Tok, hint: Vec<String>) -> Self {
        ParserError::UnexpectedToken(tok.span, tok.ty, tok.value.to_string(),
                                     hint.into_boxed_slice())
    }

    pub fn into_report(self, src: &str) -> Report<Span> {
        match self {
            ParserError::LexerError(e) => e.into_report(src),
            ParserError::UnexpectedToken(span, _, value, hint) =>
                failure(format!("Unexpected token: '{}'", value),
                        (hint_msg(&hint), span), []),
            ParserError::FloatParseError(span, value, msg) =>
                failure(format!("Could not parse float: '{}'", value),
                        (hint_msg(&[msg]), span), []),
            ParserError::IntParseError(span, value, msg) =>
                failure(format!("Could not parse integer: '{}'", value),
                        (hint_msg(&[msg]), span), []),
        }
    }
}

type PResult<T> = Result<T, ParserError>;

type AstRes<'a> = PResult<Spanned<Ast<'a>>>;

pub struct Parser<'a> {
    lexer: LexerIterator<'a>,
    end_pos: usize,
}

enum OpRule {
    Unary(&'static [&'static str]),
    UnaryTy(TokType),
    Binary(&'static [&'static str]),
}
const OP_RULES: &'static [OpRule] = &[
    OpRule::Binary(&["||"]),
    OpRule::Binary(&["&&"]),
    OpRule::Unary(&["!"]),
    OpRule::Binary(&["<", ">", "<=", ">=", "==", "!=", "===", "!=="]),
    OpRule::Binary(&["|", "&", "^"]),
    OpRule::Binary(&["<<", ">>"]),
    OpRule::Binary(&["++"]),
    OpRule::Binary(&["+", "-"]),
    OpRule::Binary(&["*", "/", "/.", "%"]),
    OpRule::Unary(&["-", "~"]),
    OpRule::Binary(&["**"]),
    OpRule::UnaryTy(TokType::Ellipsis),
];

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>, src: &'a str) -> Self {
        Parser {
            lexer: LexerIterator::new(lexer),
            end_pos: src.len(),
        }
    }

    fn next(&'a self) -> PResult<Tok<'a>> {
        match self.lexer.next() {
            Some(Ok(tok)) => Ok(tok),
            Some(Err(e)) => Err(ParserError::LexerError(e)),
            None => Err(ParserError::LexerError(LexerError::UnexpectedEof)),
        }
    }

    fn next_match(&'a self, ty: TokType) -> PResult<Tok<'a>> {
        match self.next() {
            Ok(tok) => if tok.ty == ty {
                Ok(tok)
            } else {
                Err(ParserError::unexpected(tok, vec![ty.name().to_string()]))
            },
            Err(e) => Err(e),
        }
    }

    fn next_match_of_with_options(&'a self, types: &[TokType], options: impl IntoIterator<Item = String>) -> PResult<Tok<'a>> {
        match self.next() {
            Ok(tok) => if types.contains(&tok.ty) {
                Ok(tok)
            } else {
                let mut hint = types.into_iter()
                    .map(|ty| ty.name().to_string())
                    .collect::<Vec<_>>();
                hint.extend(options);
                Err(ParserError::unexpected(tok, hint))
            },
            Err(e) => Err(e),
        }
    }

    fn next_match_of(&'a self, types: &[TokType]) -> PResult<Tok<'a>> {
        self.next_match_of_with_options(types, [])
    }

    fn peek(&'a self) -> PResult<Option<Tok<'a>>> {
        match self.lexer.peek() {
            Some(Ok(tok)) => Ok(Some(tok)),
            Some(Err(e)) => Err(ParserError::LexerError(e)),
            None => Ok(None),
        }
    }

    fn filter_tok(tok: PResult<Option<Tok<'a>>>, filter: impl FnOnce(&Tok<'a>) -> bool) -> PResult<Option<Tok<'a>>> {
        if let Ok(Some(tok)) = tok {
            if filter(&tok) {
                Ok(Some(tok))
            } else {
                Ok(None)
            }
        } else {
            tok
        }
    }

    fn peek_match(&'a self, ty: TokType) -> PResult<Option<Tok<'a>>> {
        Self::filter_tok(self.peek(), |tok| tok.ty == ty)
    }

    fn peek_match_of(&'a self, types: &[TokType]) -> PResult<Option<Tok<'a>>> {
        Self::filter_tok(self.peek(), |tok| types.contains(&tok.ty))
    }

    fn peek_match_f(&'a self, func: impl FnOnce(&Tok<'a>) -> bool) -> PResult<Option<Tok<'a>>> {
        Self::filter_tok(self.peek(), func)
    }

    fn take_if_tok(&'a self, tok: PResult<Option<Tok<'a>>>) -> PResult<Option<Tok<'a>>> {
        if let Ok(Some(tok)) = tok {
            self.next()?;
            Ok(Some(tok))
        } else {
            tok
        }
    }

    fn peek_take(&'a self, ty: TokType) -> PResult<Option<Tok<'a>>> {
        self.take_if_tok(self.peek_match(ty))
    }

    fn peek_take_f(&'a self, func: impl FnOnce(&Tok<'a>) -> bool) -> PResult<Option<Tok<'a>>> {
        self.take_if_tok(self.peek_match_f(func))
    }

    pub fn parse(&'a self) -> AstRes<'a> {
        self.parse_block(false, false, false, Self::parse_top_level)
    }

    fn parse_block(&'a self, start_brace: bool, end_brace: bool,
                   can_return_value: bool, parse: impl Fn(&'a Self) -> AstRes<'a>) -> AstRes<'a> {
        let start = self.peek()?.map_or(self.end_pos, |tok| tok.span.start);
        let mut end = start;

        if start_brace {
            self.next_match(TokType::LBrace)?;
        }

        let mut code = vec![];
        let returns_last = loop {
            if end_brace {
                if let Some(tok) = self.peek_take(TokType::RBrace)? {
                    end = tok.span.end;
                    break false;
                }
            }

            if !end_brace && self.peek()?.is_none() {
                break false;
            }
            code.push(parse(self)?);

            if !can_return_value {
                if let Some(Tok { span, ty: TokType::RBrace, .. }) = self.lexer.last() {
                    end = span.end;
                } else {
                    end = self.next_match(TokType::Semicolon)?.span.end;
                }
            } else {
                if let Some(tok) = self.peek_take(TokType::RBrace)? {
                    end = tok.span.end;
                    break true;
                } else {
                    end = self.next_match(TokType::Semicolon)?.span.end;
                }
            }
        };

        Ok(Ast::Block(code, returns_last).spanned(start..end))
    }

    fn parse_comma_separated_to_f<T>(&'a self, start: Option<TokType>, end: impl Fn(&Tok<'a>) -> bool,
                                     end_name: &str,
                                     func: impl Fn(&'a Self) -> PResult<T>,
                                     to: &mut Vec<T>) -> PResult<Span> {
        let start_pos = if let Some(ty) = start {
            self.next_match(ty)?.span.start
        } else {
            self.peek()?.map_or(self.end_pos, |tok| tok.span.start)
        };
        let end_pos;

        loop {
            if let Some(tok) = self.peek_take_f(&end)? {
                end_pos = tok.span.end;
                break;
            }

            to.push(func(self)?);

            if self.peek_take(TokType::Comma)?.is_none() {
                let end_tok = self.next()?;
                if !end(&end_tok) {
                    return Err(ParserError::unexpected(end_tok, vec![
                        TokType::Comma.name().to_string(), end_name.to_string()]))
                }
                end_pos = end_tok.span.end;
                break;
            }
        }

        Ok(start_pos..end_pos)
    }

    fn parse_comma_separated_to<T>(&'a self, start: Option<TokType>, end: TokType,
                                   func: impl Fn(&'a Self) -> PResult<T>,
                                   to: &mut Vec<T>) -> PResult<Span> {
        self.parse_comma_separated_to_f(start, |tok| tok.ty == end, end.name(), func, to)
    }

    fn parse_comma_separated<T>(&'a self, start: Option<TokType>, end: TokType,
                                func: impl Fn(&'a Self) -> PResult<T>) -> PResult<Spanned<Vec<T>>> {
        let mut to = vec![];
        let span = self.parse_comma_separated_to(start, end, func, &mut to)?;
        spanned_ok(span, to)
    }

    fn parse_type_or_none_q(&'a self) -> PResult<Spanned<Option<Box<TypeAst<'a>>>>> {
        Ok(if let Some(tok) = self.peek_take(TokType::Question)? {
            None.spanned(tok.span)
        } else {
            let (ty, span) = self.parse_type()?;
            Some(Box::new(ty)).spanned(span)
        })
    }

    fn parse_type_constraint(&'a self) -> PResult<Spanned<TypeConstraintAst<'a>>> {
        if let Some(tok) = self.peek_take(TokType::LBrack)? {
            let params = self.parse_comma_separated(
                None, TokType::RBrack, Parser::parse_unnamed_func_param)?;
            self.next_match(TokType::Arrow)?;
            let res = self.parse_type_or_none_q()?;
            spanned_ok(tok.span.start..res.1.end, TypeConstraintAst::Index(params.0, res))
        } else {
            let (ty, span) = self.parse_type()?;
            spanned_ok(span, TypeConstraintAst::Type(Box::new(ty)))
        }
    }

    fn parse_type(&'a self) -> PResult<Spanned<TypeAst<'a>>> {
        let tok = self.next_match_of(&[
            TokType::Id, TokType::LParen, TokType::LBrace,
            TokType::LBrack, TokType::KwFn, TokType::Hash,
        ])?;

        match tok.ty {
            TokType::Id => {
                if self.peek_match(TokType::DoubleColon)?.is_some() {
                    let mut path = vec![tok.as_spanned_str()];
                    while self.peek_take(TokType::DoubleColon)?.is_some() {
                        path.push(self.next_match(TokType::Id)?.as_spanned_str());
                    }
                    spanned_ok(tok.span.start..path.last().unwrap().1.end, TypeAst::Path(path))
                } else {
                    spanned_ok(tok.span, TypeAst::Ident(tok.value))
                }
            },
            TokType::LParen => {
                let types = self.parse_comma_separated(None, TokType::RParen, Parser::parse_type)?;
                spanned_ok(tok.span.start..types.1.end, TypeAst::Tuple(types.0))
            },
            TokType::LBrack => {
                let ty = self.parse_type()?;
                let count = if self.peek_take(TokType::Semicolon)?.is_some() {
                    let count = self.next_match(TokType::LitInteger)?;
                    Some(usize::from_str(count.value).map_err(
                        |err| ParserError::IntParseError(
                            count.span.clone(), count.value.to_string(), err.to_string()))?
                        .spanned(count.span))
                } else {
                    None
                };
                let end = self.next_match(TokType::RBrack)?;
                spanned_ok(tok.span.start..end.span.end, TypeAst::NTuple(Box::new(ty), count))
            },
            TokType::LBrace => {
                let constraints = self.parse_comma_separated(
                    None, TokType::RBrace, Parser::parse_type_constraint)?;
                spanned_ok(tok.span.start..constraints.1.end, TypeAst::Constraints(constraints.0))
            },
            TokType::KwFn => {
                let params = self.parse_comma_separated(
                    Some(TokType::LParen), TokType::RParen, Parser::parse_unnamed_func_param)?;
                self.peek_take(TokType::Arrow)?;
                let res = self.parse_type_or_none_q()?;
                spanned_ok(tok.span.start..res.1.end, TypeAst::Function(params.0, res))
            },
            TokType::Hash => {
                let val = self.parse_expression()?;
                spanned_ok(tok.span.start..val.1.end, TypeAst::Typeof(Box::new(val.0)))
            },
            _ => panic!("Unexpected token type: {:?}", tok.ty),
        }
    }

    fn parse_unnamed_func_param(&'a self) -> PResult<Spanned<UnnamedFunctionParam<'a>>> {
        let reference = self.peek_take_f(
            |tok| tok.ty == TokType::Operator && tok.value == "&")?;
        let ty = self.parse_type()?;
        spanned_ok(reference.as_ref().map_or(ty.1.start, |tok| tok.span.start)..ty.1.end, UnnamedFunctionParam {
            ty,
            reference: reference.map(|tok| tok.span),
        })
    }

    fn parse_func_param(&'a self) -> PResult<Spanned<FunctionParam<'a>>> {
        let reference = self.peek_take_f(
            |tok| tok.ty == TokType::Operator && tok.value == "&")?;
        let ident = self.next_match(TokType::Id)?.as_spanned_str();
        self.next_match(TokType::Colon)?;
        let ty = self.parse_type()?;
        spanned_ok(reference.as_ref().map_or(ident.1.start, |tok| tok.span.start)..ty.1.end, FunctionParam {
            name: ident,
            ty,
            reference: reference.map(|tok| tok.span),
        })
    }

    fn parse_optional_colon_type(&'a self) -> PResult<Option<Spanned<TypeAst<'a>>>> {
        if self.peek_take(TokType::Colon)?.is_some() {
            Ok(Some(self.parse_type()?))
        } else {
            Ok(None)
        }
    }

    fn parse_struct_element(&'a self) -> PResult<Spanned<StructElement<'a>>> {
        let tok = self.next_match_of(&[
            TokType::KwLet, TokType::KwConst, TokType::KwType,
            TokType::KwFn, TokType::KwStatic,
        ])?;
        let ident = self.next_match(TokType::Id)?.as_spanned_str();
        let res = match tok.ty {
            TokType::KwLet => {
                self.next_match(TokType::Colon)?;
                let ty = self.parse_type()?;
                spanned_ok(tok.span.start..ty.1.end, StructElement::Field(ident, ty))
            },
            TokType::KwConst => {
                let ty = self.parse_optional_colon_type()?;
                self.next_match(TokType::Assign)?;
                let value = self.parse_expression()?;
                spanned_ok(tok.span.start..value.1.end, StructElement::Const(ident, ty, Box::new(value)))
            },
            TokType::KwType => {
                self.next_match(TokType::Assign)?;
                let ty = self.parse_type()?;
                spanned_ok(tok.span.start..ty.1.end, StructElement::Type(ident, ty))
            },
            TokType::KwFn => {
                let lparen = self.next_match(TokType::LParen)?;

                let method_self = if self.peek_take_f(|tok| tok.ty == TokType::Operator && tok.value == "*")?.is_some() {
                    self.next_match(TokType::KwSelf)?;
                    StructMethodSelf::Copy
                } else if self.peek_take(TokType::KwConst)?.is_some() {
                    self.next_match(TokType::KwSelf)?;
                    StructMethodSelf::ConstRef
                } else if self.peek_take(TokType::KwSelf)?.is_some() {
                    StructMethodSelf::Ref
                } else {
                    StructMethodSelf::Static
                };
                
                let params = if method_self == StructMethodSelf::Static || self.peek_take(TokType::Comma)?.is_some() {
                    self.parse_comma_separated(None, TokType::RParen, Self::parse_func_param)?
                } else {
                    self.next_match(TokType::RParen)?;
                    vec![].spanned(lparen.span)
                };
                let result = if self.peek_take(TokType::Arrow)?.is_some() {
                    Some(self.parse_type()?)
                } else {
                    None
                };
                let body = self.parse_block(true, true, true, Self::parse_statement)?;
                spanned_ok(tok.span.start..body.1.end, StructElement::Method(ident, method_self, params.0, result, Box::new(body)))
            },
            TokType::KwStatic => {
                let ty = self.parse_optional_colon_type()?;
                self.next_match(TokType::Assign)?;
                let value = self.parse_expression()?;
                spanned_ok(tok.span.start..value.1.end, StructElement::StaticField(ident, ty, Box::new(value)))
            },
            _ => panic!("Unexpected token type: {:?}", tok.ty),
        };
        if tok.ty != TokType::KwFn {
            self.next_match(TokType::Semicolon)?;
        }
        res
    }

    fn parse_top_level(&'a self) -> AstRes<'a> {
        let tok = self.next_match_of(&[
            TokType::KwFn, TokType::KwConst, TokType::KwType,
            TokType::KwStruct, TokType::KwEnum, TokType::KwNamespace,
        ])?;
        match tok.ty {
            TokType::KwFn => {
                let ident = self.next_match(TokType::Id)?.as_spanned_str();
                let params = self.parse_comma_separated(Some(TokType::LParen), TokType::RParen, Self::parse_func_param)?;
                let result = if self.peek_take(TokType::Arrow)?.is_some() {
                    Some(self.parse_type()?)
                } else {
                    None
                };
                let code = self.parse_block(true, true, true, Self::parse_statement)?;
                spanned_ok(tok.span.start..code.1.end, Ast::Function(ident, params.0, result, Box::new(code)))
            },
            TokType::KwConst => {
                let ident = self.next_match(TokType::Id)?.as_spanned_str();
                let ty = self.parse_optional_colon_type()?;
                self.next_match(TokType::Assign)?;
                let value = self.parse_expression()?;
                spanned_ok(tok.span.start..value.1.end, Ast::Const(ident, ty, Box::new(value)))
            },
            TokType::KwType => {
                let ident = self.next_match(TokType::Id)?.as_spanned_str();
                self.next_match(TokType::Assign)?;
                let ty = self.parse_type()?;
                spanned_ok(tok.span.start..ty.1.end, Ast::Type(ident, ty))
            },
            TokType::KwStruct => {
                let ident = self.next_match(TokType::Id)?.as_spanned_str();
                let lbrace = self.next_match(TokType::LBrace)?;
                let mut elements = vec![];
                let end = loop {
                    if let Some(tok) = self.peek_take(TokType::RBrace)? {
                        break tok.span.end;
                    }
                    elements.push(self.parse_struct_element()?);
                };
                spanned_ok(tok.span.start..end, Ast::Struct(ident, elements.spanned(lbrace.span.start..end)))
            },
            TokType::KwEnum => {
                let ident = self.next_match(TokType::Id)?.as_spanned_str();
                let values = self.parse_comma_separated(
                    Some(TokType::LBrace), TokType::RBrace,
                    |parser| {
                        let ident = parser.next_match(TokType::Id)?.as_spanned_str();
                        let value = if parser.peek_take(TokType::Assign)?.is_some() {
                            let neg = parser.peek_take_f(
                                |tok| tok.ty == TokType::Operator && tok.value == "-")?
                                .map_or(1., |_| -1.);
                            let tok = parser.next_match_of(&[TokType::LitInteger, TokType::LitFloat])?;
                            let val = f64::from_str(tok.value).map_err(
                                |err| ParserError::FloatParseError(tok.span, tok.value.to_string(), err.to_string()))?;
                            Some(val * neg)
                        } else {
                            None
                        };
                        Ok((ident, value))
                    })?;
                spanned_ok(tok.span.start..values.1.end, Ast::Enum(ident, values))
            },
            TokType::KwNamespace => {
                let ident = self.next_match(TokType::Id)?.as_spanned_str();
                let block = self.parse_block(
                    true, true, false,
                    |parser| parser.parse_top_level())?;
                spanned_ok(tok.span.start..block.1.end, Ast::Namespace(ident, Box::new(block)))
            },
            _ => panic!("Unexpected token type: {:?}", tok.ty),
        }
    }

    fn parse_match_pattern(&'a self) -> PResult<Spanned<MatchPatAst<'a>>> {
        let tok = self.next_match_of(&[
            TokType::Underscore, TokType::Id,
        ])?;
        match tok.ty {
            TokType::Underscore => {
                spanned_ok(tok.span, MatchPatAst::Underscore)
            },
            TokType::Id => {
                spanned_ok(tok.span, MatchPatAst::Variable(tok.value))
            },
            _ => panic!("Unexpected token type: {:?}", tok.ty),
        }
    }

    fn parse_statement(&'a self) -> AstRes<'a> {
        let tok = self.peek_match_of(&[
            TokType::KwLet, TokType::KwConst, TokType::KwWhile,
            TokType::KwFor, TokType::KwBreak, TokType::KwContinue,
        ])?;

        let tok = if tok.is_some() {
            self.next()?
        } else {
            return self.parse_expression()
        };

        match tok.ty {
            TokType::KwLet => {
                let pat = self.parse_match_pattern()?;
                let ty = self.parse_optional_colon_type()?;
                self.next_match(TokType::Assign)?;
                let value = self.parse_expression()?;
                spanned_ok(tok.span.start..value.1.end, Ast::Let(pat, ty, Box::new(value)))
            },
            TokType::KwConst => {
                let ident = self.next_match(TokType::Id)?.as_spanned_str();
                let ty = self.parse_optional_colon_type()?;
                self.next_match(TokType::Assign)?;
                let value = self.parse_expression()?;
                spanned_ok(tok.span.start..value.1.end, Ast::Const(ident, ty, Box::new(value)))
            },
            TokType::KwWhile => {
                let cond = self.parse_expression()?;
                let code = self.parse_block(true, true, false, Self::parse_statement)?;
                spanned_ok(tok.span.start..code.1.end, Ast::While(Box::new(cond), Box::new(code)))
            },
            TokType::KwFor => {
                let pat = self.parse_match_pattern()?;
                self.next_match(TokType::KwIn)?;
                let value = self.parse_expression()?;
                let code = self.parse_block(true, true, false, Self::parse_statement)?;
                spanned_ok(tok.span.start..code.1.end, Ast::For(pat, Box::new(value), Box::new(code)))
            },
            TokType::KwBreak => {
                spanned_ok(tok.span, Ast::Break)
            },
            TokType::KwContinue => {
                spanned_ok(tok.span, Ast::Continue)
            },
            _ => panic!("Unexpected token type: {:?}", tok.ty),
        }
    }

    fn parse_expression(&'a self) -> AstRes<'a> {
        self.parse_assignment()
    }

    fn parse_assignment(&'a self) -> AstRes<'a> {
        let left = self.parse_cast()?;
        if self.peek_take(TokType::Assign)?.is_some() {
            let right = self.parse_cast()?;
            spanned_ok(left.1.start..right.1.end, Ast::Assign(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    fn parse_cast(&'a self) -> AstRes<'a> {
        let mut left = self.parse_range()?;
        while self.peek_take(TokType::KwAs)?.is_some() {
            let right = self.parse_type()?;
            left = spanned(left.1.start..right.1.end, Ast::Cast(Box::new(left), right))
        }
        Ok(left)
    }

    fn parse_range(&'a self) -> AstRes<'a> {
        let start = self.parse_operators()?;
        if self.peek_take(TokType::DoubleDot)?.is_some() {
            let end = self.parse_operators()?;
            let (end_pos, step) = if self.peek_take(TokType::DoubleDot)?.is_some() {
                let step = self.parse_operators()?;
                (step.1.end, Some(Box::new(step)))
            } else {
                (end.1.end, None)
            };
            spanned_ok(start.1.start..end_pos, Ast::Range(Box::new(start), Box::new(end), step))
        } else {
            Ok(start)
        }
    }

    fn parse_operators_impl(&'a self, rules: &[OpRule], bottom: impl Fn(&'a Self) -> AstRes<'a> + Copy) -> AstRes<'a> {
        let (rule, rest) = match rules {
            [rule, rest @ ..] => (rule, rest),
            _ => return bottom(self),
        };

        match rule {
            OpRule::Unary(options) =>
                if let Some(op) = self.peek_take_f(
                    |tok| tok.ty == TokType::Operator && options.contains(&tok.value))? {
                    let value = self.parse_operators_impl(rules, bottom)?;
                    spanned_ok(op.span.start..value.1.end, Ast::Unary(op.as_spanned_str(), Box::new(value)))
                } else {
                    self.parse_operators_impl(rest, bottom)
                },
            OpRule::UnaryTy(ty) =>
                if let Some(op) = self.peek_take(*ty)? {
                    let value = self.parse_operators_impl(rules, bottom)?;
                    spanned_ok(op.span.start..value.1.end, Ast::Unary(op.as_spanned_str(), Box::new(value)))
                } else {
                    self.parse_operators_impl(rest, bottom)
                },
            OpRule::Binary(options) => {
                let mut left = self.parse_operators_impl(rest, bottom)?;
                while let Some(op) = self.peek_take_f(
                    |tok| tok.ty == TokType::Operator && options.contains(&tok.value))? {
                    let right = self.parse_operators_impl(rest, bottom)?;
                    left = spanned(left.1.start..right.1.end,
                                   Ast::Binary(Box::new(left), op.as_spanned_str(), Box::new(right)));
                }
                Ok(left)
            },
        }
    }

    fn parse_operators(&'a self) -> AstRes<'a> {
        self.parse_operators_impl(OP_RULES, Self::parse_call_index_attr)
    }

    fn parse_call_index_attr(&'a self) -> AstRes<'a> {
        let mut val = self.parse_atom()?;
        while let Some(tok) = self.peek_match_of(&[
            TokType::LParen, TokType::LBrack,
            TokType::Dot, TokType::DoubleColon,
        ])? {
            self.next()?;
            match tok.ty {
                TokType::LParen => {
                    // TODO: unpack
                    let params = self.parse_comma_separated(
                        None, TokType::RParen, Self::parse_expression)?;
                    val = spanned(val.1.start..params.1.end, Ast::Call(Box::new(val), params.0))
                },
                TokType::LBrack => {
                    // TODO: unpack
                    let params = self.parse_comma_separated(
                        None, TokType::RBrack, Self::parse_expression)?;
                    val = spanned(val.1.start..params.1.end, Ast::Index(Box::new(val), params.0))
                },
                TokType::Dot => {
                    let name = self.lexer.lexer().lex_attribute()
                        .map_err(ParserError::LexerError)?.as_spanned_str();
                    val = spanned(val.1.start..name.1.end, Ast::Attr(Box::new(val), false, name))
                },
                TokType::DoubleColon => {
                    let name = self.next_match(TokType::Id)?.as_spanned_str();
                    val = spanned(val.1.start..name.1.end, Ast::Attr(Box::new(val), true, name))
                },
                _ => panic!("Unexpected token type: {:?}", tok.ty),
            }
        }
        Ok(val)
    }

    fn parse_lambda_param(&'a self) -> PResult<Spanned<LambdaParam<'a>>> {
        let reference = self.peek_take_f(
            |tok| tok.ty == TokType::Operator && tok.value == "&")?;
        let ident = self.next_match(TokType::Id)?.as_spanned_str();
        let ty = self.parse_optional_colon_type()?;
        spanned_ok(reference.as_ref().map_or(
            ident.1.start, |tok| tok.span.start)..ty.as_ref().map_or(
            ident.1.end, |ty| ty.1.end),LambdaParam {
            name: ident,
            ty,
            reference: reference.map(|tok| tok.span),
        })
    }

    fn parse_lambda_capture(&'a self) -> PResult<Spanned<LambdaCapture<'a>>> {
        if let Some(reference) = self.peek_take_f(
            |tok| tok.ty == TokType::Operator && tok.value == "&")? {
            let ident = self.next_match(TokType::Id)?.as_spanned_str();
            spanned_ok(reference.span.start..ident.1.end, LambdaCapture::Ref(reference.span, ident))
        } else {
            let ident = self.next_match(TokType::Id)?.as_spanned_str();
            if self.peek_take(TokType::Assign)?.is_some() {
                let value = self.parse_expression()?;
                spanned_ok(ident.1.start..value.1.end, LambdaCapture::Value(ident, Box::new(value)))
            } else {
                spanned_ok(ident.1.clone(), LambdaCapture::Copy(ident))
            }
        }
    }

    fn parse_atom(&'a self) -> AstRes<'a> {
        let tok = self.next()?;

        match tok.ty {
            TokType::KwIf => {
                let cond = self.parse_expression()?;
                let b_true = self.parse_block(
                    true, true, true, Self::parse_statement)?;
                let (end_pos, b_false) = if self.peek_take(TokType::KwElse)?.is_some() {
                    let block = self.parse_block(
                        true, true, true, Self::parse_statement)?;
                    (block.1.end, Some(Box::new(block)))
                } else {
                    (b_true.1.end, None)
                };
                spanned_ok(tok.span.start..end_pos, Ast::If(Box::new(cond), Box::new(b_true), b_false))
            },
            TokType::KwConst => {
                todo!("Comptime")
            },
            TokType::LBrace => {
                self.parse_block(false, true, true, Self::parse_statement)
            },
            TokType::LParen => {
                if let Some(end) = self.peek_take(TokType::RParen)? {
                    spanned_ok(tok.span.start..end.span.end, Ast::Tuple(vec![]))
                } else {
                    // TODO: unpack
                    let val = self.parse_expression()?;
                    if self.peek_take(TokType::Comma)?.is_some() {
                        let mut values = vec![val];
                        let span = self.parse_comma_separated_to(
                            None, TokType::RParen, Self::parse_expression, &mut values)?;
                        spanned_ok(tok.span.start..span.end, Ast::Tuple(values))
                    } else {
                        // comma is already handled
                        let end = self.next_match_of(&[TokType::RParen, TokType::Comma])?;
                        spanned_ok(tok.span.start..end.span.end, val.0)
                    }
                }
            },
            TokType::LitInteger => {
                spanned_ok(tok.span, Ast::LitInteger(tok.value))
            },
            TokType::LitFloat => {
                spanned_ok(tok.span, Ast::LitFloat(tok.value))
            },
            TokType::LitString => {
                spanned_ok(tok.span, Ast::LitString(tok.value))
            },
            TokType::LitChar => {
                spanned_ok(tok.span, Ast::LitChar(tok.value))
            },
            TokType::LitColor => {
                spanned_ok(tok.span, Ast::LitColor(tok.value))
            },
            TokType::Operator if tok.value == "|" || tok.value == "||" => {
                let start = tok.span.start;
                let params = if tok.value == "||" {
                    vec![].spanned(tok.span)
                } else {
                    let mut params = vec![];
                    let span = self.parse_comma_separated_to_f(
                        None, |tok| tok.ty == TokType::Operator && tok.value == "||",
                        "'|'", Self::parse_lambda_param, &mut params)?;
                    params.spanned(tok.span.start..span.end)
                };
                let captures = if self.peek_take(TokType::LBrack)?.is_some() {
                    self.parse_comma_separated(None, TokType::RBrack, Self::parse_lambda_capture)?.0
                } else {
                    vec![]
                };
                let result = if self.peek_take(TokType::Arrow)?.is_some() {
                    Some(self.parse_type()?)
                } else {
                    None
                };
                let code = self.parse_expression()?;
                spanned_ok(start..code.1.end, Ast::Lambda(params.0, captures, result, Box::new(code)))
            },
            TokType::Id => {
                spanned_ok(tok.span, Ast::Variable(tok.value))
            },
            TokType::Hash => {
                todo!("Macros")
            },
            TokType::DoubleColon => {
                spanned_ok(tok.span, Ast::ImplicitEnumVariable(tok.value))
            },
            _ => {
                let mut hint = [
                    TokType::KwIf, TokType::KwConst, TokType::LBrace,
                    TokType::LParen, TokType::Hash, TokType::DoubleColon,
                    TokType::Id,
                ].into_iter()
                    .map(|ty| ty.name().to_string())
                    .collect::<Vec<_>>();
                hint.extend(["literal".to_string(), "'|'".to_string()]);
                Err(ParserError::unexpected(tok, hint))
            },
        }
    }
}
