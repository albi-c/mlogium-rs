use ariadne::Source;
use parse::lex::{Lexer, LexerIterator};
use parse::parser::Parser;

const TEST_CODE: &str = r#"
struct S {
    type T = num;
    let x: num;

    fn st() {}
}

enum T {
    A, B = 3.1, C = -1,
}

fn max(a: num, b: num) {
}

fn main() -> num {
}
"#;

fn main() {
    let src = TEST_CODE;

    let lexer = Lexer::new(src);

    let iterator = LexerIterator::new(lexer);

    let mut tokens = vec![];
    while let Some(tok) = iterator.next() {
        match tok {
            Ok(tok) => {
                tokens.push(tok);
            },
            Err(err) => {
                err.into_report(src).print(Source::from(src)).unwrap();
                std::process::exit(1);
            }
        }
    };

    println!("{:?}", tokens);

    let lexer = Lexer::new(src);
    let parser = Parser::new(lexer, src);
    let ast = parser.parse();

    match ast {
        Ok(ast) => println!("{:?}", ast),
        Err(err) => {
            err.into_report(src).print(Source::from(src)).unwrap();
            std::process::exit(1);
        }
    }
}
