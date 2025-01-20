use parser::Parser;
pub mod bytecode;
pub mod codegen;
mod intern;
mod lexer;
pub mod parser;
#[cfg(test)]
mod tests;
mod vm;

fn main() {
    let content = include_str!("../examples/fizzbuzz.pty");
    let parser = Parser::new(content);
    let ast = match parser.parse_root() {
        Ok(ast) => ast,
        Err(err) => panic!("{err:?}"),
    };
    let bytecode = codegen::codegen(&ast);
    std::fs::write("output.ptyb", &bytecode).unwrap();
    vm::execute_bytecode(&bytecode);
}
