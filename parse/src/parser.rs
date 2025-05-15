use std::str::FromStr;
use ariadne::Report;
use crate::ast::{Ast, FunctionParam, MatchPatAst, StructElement, StructMethodSelf, TypeAst, TypeConstraintAst, UnnamedFunctionParam};
use crate::error::{failure, hint_msg};
use crate::lex::{Lexer, LexerError, LexerIterator, Tok, TokType};
use crate::span::{spanned_ok, Span, Spannable, Spanned};

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

    fn parse_comma_separated<T>(&'a self, start: Option<TokType>, end: TokType,
                                func: impl Fn(&'a Self) -> PResult<T>) -> PResult<Spanned<Vec<T>>> {
        let start_pos = if let Some(ty) = start {
            self.next_match(ty)?.span.start
        } else {
            self.peek()?.map_or(self.end_pos, |tok| tok.span.start)
        };
        let end_pos;

        let mut values = vec![];
        loop {
            if let Some(tok) = self.peek_take(end)? {
                end_pos = tok.span.end;
                break;
            }

            values.push(func(self)?);

            if self.peek_take(TokType::Comma)?.is_none() {
                end_pos = self.next_match_of(&[end, TokType::Comma])?.span.end;
                break;
            }
        }

        Ok(values.spanned(start_pos..end_pos))
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
            reference: reference.map(|tok| ().spanned(tok.span)),
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
            reference: reference.map(|tok| ().spanned(tok.span)),
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
        // TODO: when parsing {expr}.{attr}, use special lexer fn for attr -
        // TODO: - prevent two int attrs from merging as float
        todo!()
    }
}
