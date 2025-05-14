use crate::span::Spanned;

#[derive(Debug)]
pub enum TypeAst<'a> {
    Ident(&'a str),
}

#[derive(Debug)]
pub struct FunctionParam<'a> {
    pub name: Spanned<&'a str>,
    pub ty: Spanned<TypeAst<'a>>,
    pub reference: bool,
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
    Method(Spanned<&'a str>, StructMethodSelf, Spanned<Vec<FunctionParam<'a>>>,
           Option<Spanned<TypeAst<'a>>>, Box<Spanned<Ast<'a>>>),
}

#[derive(Debug)]
pub enum Ast<'a> {
    LitString(&'a str),

    Block(Vec<Spanned<Ast<'a>>>, bool),
    Function(Spanned<&'a str>, Spanned<Vec<FunctionParam<'a>>>,
             Option<Spanned<TypeAst<'a>>>, Box<Spanned<Ast<'a>>>),
    Const(Spanned<&'a str>, Option<Spanned<TypeAst<'a>>>, Box<Spanned<Ast<'a>>>),
    Type(Spanned<&'a str>, Spanned<TypeAst<'a>>),
    Struct(Spanned<&'a str>, Spanned<Vec<Spanned<StructElement<'a>>>>),
    Enum(Spanned<&'a str>, Spanned<Vec<(Spanned<&'a str>, Option<f64>)>>),
    Namespace(Spanned<&'a str>, Box<Spanned<Ast<'a>>>),
}
