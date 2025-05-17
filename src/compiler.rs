use ariadne::Report;
use smol_str::{SmolStr, ToSmolStr};
use parse::ast::{Ast, StructElement, StructMethodSelf};
use parse::error::failure;
use parse::span::{Span, Spanned};
use crate::context::Ctx;
use crate::tree::{Tree, TreeNode};

#[derive(Debug)]
pub enum CompilerError {
    ValueAlreadyDefined(SmolStr, Span, Span),
    TypeAlreadyDefined(SmolStr, Span, Span),
}

impl CompilerError {
    pub fn into_error<'a>(self) -> Report<'a, Span> {
        match self {
            CompilerError::ValueAlreadyDefined(name, span, prev) =>
                failure(format!("Value already defined: '{}'", name),
                        ("Here".to_string(), span), [("Previous definition".to_string(), prev)]),
            CompilerError::TypeAlreadyDefined(name, span, prev) =>
                failure(format!("Type already defined: '{}'", name),
                        ("Here".to_string(), span), [("Previous definition".to_string(), prev)]),
        }
    }
}

type CRes<T> = Result<T, CompilerError>;

trait TreeExt {
    fn insert_val(&mut self, name: &Spanned<&str>) -> Result<&mut TreeNode<SmolStr, ()>, CompilerError>;
    fn insert_ty(&mut self, name: &Spanned<&str>) -> Result<&mut TreeNode<SmolStr, ()>, CompilerError>;
}

impl TreeExt for Tree<SmolStr, ()> {
    fn insert_val(&mut self, name: &Spanned<&str>) -> Result<&mut TreeNode<SmolStr, ()>, CompilerError> {
        self.insert(name.1.clone(), name.0.to_smolstr(), ())
            .map_err(|prev| CompilerError::ValueAlreadyDefined(name.0.to_smolstr(), name.1.clone(), prev))
    }
    fn insert_ty(&mut self, name: &Spanned<&str>) -> Result<&mut TreeNode<SmolStr, ()>, CompilerError> {
        self.insert(name.1.clone(), name.0.to_smolstr(), ())
            .map_err(|prev| CompilerError::TypeAlreadyDefined(name.0.to_smolstr(), name.1.clone(), prev))
    }
}

pub struct Compiler<'a> {
    ctx: &'a mut Ctx,
}

impl<'a> Compiler<'a> {
    pub fn new(ctx: &'a mut Ctx) -> Self {
        Self {
            ctx,
        }
    }

    pub fn compile(&mut self, ast: Spanned<Ast>) -> CRes<()> {
        let globals = &mut self.ctx.globals;
        Self::scan_top_level(&ast, &mut globals.val, &mut globals.ty)
    }
    
    pub fn scan_struct_element(element: &Spanned<StructElement>,
                               g_val: &mut Tree<SmolStr, ()>,
                               g_ty: &mut Tree<SmolStr, ()>) -> CRes<()> {
        match &element.0 {
            StructElement::Type(name, _) => {
                g_ty.insert_ty(name)?;
            },
            StructElement::Const(name, _, _) => {
                g_val.insert_val(name)?;
            },
            StructElement::Field(_name, _) => {},
            StructElement::StaticField(name, _, _) => {
                g_val.insert_val(name)?;
            },
            StructElement::Method(name, self_type, _, _, _) => {
                match *self_type {
                    StructMethodSelf::Static => {
                        g_val.insert_val(name)?;
                    },
                    _ => {},
                }
            },
        }
        Ok(())
    }

    pub fn scan_top_level(ast: &Spanned<Ast>,
                          g_val: &mut Tree<SmolStr, ()>,
                          g_ty: &mut Tree<SmolStr, ()>) -> CRes<()> {
        match &ast.0 {
            Ast::Block(items, returns_last) => {
                assert!(!returns_last);
                for item in items {
                    Self::scan_top_level(item, g_val, g_ty)?;
                }
            },
            Ast::Function(name, _, _, _) => {
                g_val.insert_val(name)?;
            },
            Ast::Const(name, _, _) => {
                g_val.insert_val(name)?;
            },
            Ast::Type(name, _) => {
                g_ty.insert_ty(name)?;
            },
            Ast::Struct(name, elements) => {
                let g_val = g_val.insert_val(name)?;
                let g_ty = g_ty.insert_ty(name)?;
                for elem in &elements.0 {
                    Self::scan_struct_element(elem, g_val.tree_mut(), g_ty.tree_mut())?;
                }
            },
            Ast::Enum(name, _) => {
                g_ty.insert_ty(name)?;
            },
            Ast::Namespace(name, body) => {
                let g_val = g_val.insert_val(name)?;
                let g_ty = g_ty.insert_ty(name)?;
                Self::scan_top_level(body, g_val.tree_mut(), g_ty.tree_mut())?;
            },
            _ => panic!("Invalid top level item: {:?}", ast)
        }
        Ok(())
    }
}
