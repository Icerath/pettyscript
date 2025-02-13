use crate::{
    codegen,
    hir::{self},
    parser::parse,
};

pub fn compile(src: &str) -> miette::Result<Vec<u8>> {
    let std = parse(include_str!("../lib/std.pty"))?;
    let ast = parse(src)?;

    let mut hir = hir::Lowering::new(src);
    let mut std = hir.block(&std)?;
    let block = hir.block(&ast)?;
    std.items.extend(block.items);
    codegen::codegen(&std, hir.subs, hir.main_fn)
}
