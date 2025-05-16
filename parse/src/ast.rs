use crate::span::{Span, Spanned};

pub type AstPath<'a> = Vec<Spanned<&'a str>>;

#[derive(Debug)]
pub enum TypeConstraintAst<'a> {
    Type(Box<TypeAst<'a>>),
    Index(Vec<Spanned<UnnamedFunctionParam<'a>>>, Spanned<Option<Box<TypeAst<'a>>>>),
}

#[derive(Debug)]
pub enum TypeAst<'a> {
    Ident(&'a str),
    Path(AstPath<'a>),
    Tuple(Vec<Spanned<TypeAst<'a>>>),
    NTuple(Box<Spanned<TypeAst<'a>>>, Option<Spanned<usize>>),
    Function(Vec<Spanned<UnnamedFunctionParam<'a>>>, Spanned<Option<Box<TypeAst<'a>>>>),
    Constraints(Vec<Spanned<TypeConstraintAst<'a>>>),
    Typeof(Box<Ast<'a>>),
}

#[derive(Debug)]
pub struct UnnamedFunctionParam<'a> {
    pub ty: Spanned<TypeAst<'a>>,
    pub reference: Option<Span>,
}

#[derive(Debug)]
pub struct FunctionParam<'a> {
    pub name: Spanned<&'a str>,
    pub ty: Spanned<TypeAst<'a>>,
    pub reference: Option<Span>,
}

#[derive(Debug)]
pub struct LambdaParam<'a> {
    pub name: Spanned<&'a str>,
    pub ty: Option<Spanned<TypeAst<'a>>>,
    pub reference: Option<Span>,
}

#[derive(Debug)]
pub enum LambdaCapture<'a> {
    Copy(Spanned<&'a str>),
    Ref(Span, Spanned<&'a str>),
    Value(Spanned<&'a str>, Box<Spanned<Ast<'a>>>),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum StructMethodSelf {
    Static,
    Ref,
    ConstRef,
    Copy,
}

#[derive(Debug)]
pub enum StructElement<'a> {
    Type(Spanned<&'a str>, Spanned<TypeAst<'a>>),
    Const(Spanned<&'a str>, Option<Spanned<TypeAst<'a>>>, Box<Spanned<Ast<'a>>>),
    Field(Spanned<&'a str>, Spanned<TypeAst<'a>>),
    StaticField(Spanned<&'a str>, Option<Spanned<TypeAst<'a>>>, Box<Spanned<Ast<'a>>>),
    Method(Spanned<&'a str>, StructMethodSelf, Vec<Spanned<FunctionParam<'a>>>,
           Option<Spanned<TypeAst<'a>>>, Box<Spanned<Ast<'a>>>),
}

#[derive(Debug)]
pub enum MatchPatAst<'a> {
    Underscore,
    Variable(&'a str),
}

#[derive(Debug)]
pub enum Ast<'a> {
    Block(Vec<Spanned<Ast<'a>>>, bool),
    Function(Spanned<&'a str>, Vec<Spanned<FunctionParam<'a>>>,
             Option<Spanned<TypeAst<'a>>>, Box<Spanned<Ast<'a>>>),
    Const(Spanned<&'a str>, Option<Spanned<TypeAst<'a>>>, Box<Spanned<Ast<'a>>>),
    Type(Spanned<&'a str>, Spanned<TypeAst<'a>>),
    Struct(Spanned<&'a str>, Spanned<Vec<Spanned<StructElement<'a>>>>),
    Enum(Spanned<&'a str>, Spanned<Vec<(Spanned<&'a str>, Option<f64>)>>),
    Namespace(Spanned<&'a str>, Box<Spanned<Ast<'a>>>),
    Let(Spanned<MatchPatAst<'a>>, Option<Spanned<TypeAst<'a>>>, Box<Spanned<Ast<'a>>>),
    While(Box<Spanned<Ast<'a>>>, Box<Spanned<Ast<'a>>>),
    For(Spanned<MatchPatAst<'a>>, Box<Spanned<Ast<'a>>>, Box<Spanned<Ast<'a>>>),
    Break,
    Continue,

    Assign(Box<Spanned<Ast<'a>>>, Box<Spanned<Ast<'a>>>),
    Cast(Box<Spanned<Ast<'a>>>, Spanned<TypeAst<'a>>),
    Range(Box<Spanned<Ast<'a>>>, Box<Spanned<Ast<'a>>>, Option<Box<Spanned<Ast<'a>>>>),
    Unary(Spanned<&'a str>, Box<Spanned<Ast<'a>>>),
    Binary(Box<Spanned<Ast<'a>>>, Spanned<&'a str>, Box<Spanned<Ast<'a>>>),
    Call(Box<Spanned<Ast<'a>>>, Vec<Spanned<Ast<'a>>>),
    Index(Box<Spanned<Ast<'a>>>, Vec<Spanned<Ast<'a>>>),
    Attr(Box<Spanned<Ast<'a>>>, bool, Spanned<&'a str>),

    If(Box<Spanned<Ast<'a>>>, Box<Spanned<Ast<'a>>>, Option<Box<Spanned<Ast<'a>>>>),
    Tuple(Vec<Spanned<Ast<'a>>>),
    Lambda(Vec<Spanned<LambdaParam<'a>>>, Vec<Spanned<LambdaCapture<'a>>>,
           Option<Spanned<TypeAst<'a>>>, Box<Spanned<Ast<'a>>>),

    Variable(&'a str),
    ImplicitEnumVariable(&'a str),
    
    LitInteger(&'a str),
    LitFloat(&'a str),
    LitString(&'a str),
    LitChar(&'a str),
    LitColor(&'a str),
}
