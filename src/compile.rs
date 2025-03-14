use crate::{codegen, mir, parse::parse, ty::TyCtx};

pub fn compile(src: &str) -> miette::Result<Vec<u8>> {
    let std = parse(include_str!("../lib/std.pty"))?;
    let ast = parse(src)?;

    let mut tcx = TyCtx::default();
    let mut mir = mir::Lowering::new(src, &mut tcx);
    let mut std = mir.block(&std)?;
    let block = mir.block(&ast)?;
    std.items.extend(block.items);

    let global_scope = mir.global_scope_size() as u32;
    codegen::codegen(&std, mir.tcx, mir.main_fn, global_scope)
}
