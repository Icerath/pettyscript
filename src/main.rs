use parser::Parser;

mod lexer;
mod parser;
#[cfg(test)]
mod tests;

fn main() {
    let content = include_str!("../examples/fizzbuzz.pty");
    let parser = Parser::new(content);
    match parser.parse_root() {
        Ok(stmts) => println!("{stmts:#?}"),
        Err(err) => eprintln!("{err:?}"),
    }
}
