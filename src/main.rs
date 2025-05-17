mod context;
mod compiler;
mod tree;

use ariadne::Source;
use parse::lex::{Lexer, LexerIterator};
use parse::parser::Parser;
use crate::compiler::Compiler;
use crate::context::Ctx;

const TEST_CODE: &str = r#"
fn main() -> num {
    test();
    0
}

fn test() {}
"#;

fn main() {
    let src = TEST_CODE;

    let lexer = Lexer::new(src);
    let parser = Parser::new(lexer, src);
    let ast = parser.parse();

    let ast = match ast {
        Ok(ast) => ast,
        Err(err) => {
            err.into_report(src).eprint(Source::from(src)).unwrap();
            std::process::exit(1);
        },
    };

    let mut ctx = Ctx::new();
    {
        let mut compiler = Compiler::new(&mut ctx);
        match compiler.compile(ast) {
            Ok(_) => {},
            Err(err) => {
                err.into_error().eprint(Source::from(src)).unwrap();
                std::process::exit(1);
            },
        }
    }
    println!("{:?}", ctx.globals);
}
