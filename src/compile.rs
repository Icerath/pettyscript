use crate::{codegen, hir, parser::parse};

pub fn compile(src: &str) -> miette::Result<Vec<u8>> {
    let ast = parse(src)?;
    let mut hir = hir::Lowering::new(src);
    let block = hir.block(&ast).unwrap();
    codegen::codegen(&block, hir.subs)
}
