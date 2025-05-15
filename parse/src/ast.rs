use crate::span::Spanned;

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
    pub reference: Option<Spanned<()>>,
}

#[derive(Debug)]
pub struct FunctionParam<'a> {
    pub name: Spanned<&'a str>,
    pub ty: Spanned<TypeAst<'a>>,
    pub reference: Option<Spanned<()>>,
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
pub enum Ast<'a> {
    LitString(&'a str),

    Block(Vec<Spanned<Ast<'a>>>, bool),
    Function(Spanned<&'a str>, Vec<Spanned<FunctionParam<'a>>>,
             Option<Spanned<TypeAst<'a>>>, Box<Spanned<Ast<'a>>>),
    Const(Spanned<&'a str>, Option<Spanned<TypeAst<'a>>>, Box<Spanned<Ast<'a>>>),
    Type(Spanned<&'a str>, Spanned<TypeAst<'a>>),
    Struct(Spanned<&'a str>, Spanned<Vec<Spanned<StructElement<'a>>>>),
    Enum(Spanned<&'a str>, Spanned<Vec<(Spanned<&'a str>, Option<f64>)>>),
    Namespace(Spanned<&'a str>, Box<Spanned<Ast<'a>>>),
}
