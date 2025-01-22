use parser::parse;
mod bytecode;
mod codegen;
mod intern;
mod lexer;
mod parser;
#[cfg(test)]
mod tests;
mod vm;

fn main() {
    let content = include_str!("../examples/lexer.pty");
    let ast = parse(content).unwrap();
    let bytecode = codegen::codegen(&ast);
    std::fs::write("output.ptyb", &bytecode).unwrap();
    vm::execute_bytecode(&bytecode);
}
