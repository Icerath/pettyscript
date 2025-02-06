use miette::Result;

use crate::{
    bytecode::{BytecodeBuilder, Instr},
    hir::*,
    parser::BinOp,
    typck::{Substitutions, Ty},
};

pub fn codegen(block: &Block, subs: Substitutions) -> Result<Vec<u8>> {
    let mut codegen = Codegen { subs, builder: BytecodeBuilder::default() };
    codegen.block(block)?;
    // TODO: Actually count this.
    codegen.builder.set_global_stack_size(64);
    Ok(codegen.builder.finish())
}

#[derive(Default)]
struct Codegen {
    subs: Substitutions,
    builder: BytecodeBuilder,
}

impl Codegen {
    fn block(&mut self, block: &Block) -> Result<()> {
        for item in &block.items {
            self.item(item)?;
        }
        Ok(())
    }

    fn item(&mut self, item: &Item) -> Result<()> {
        match item {
            Item::Function(func) => self.function(func),
            Item::Expr(expr) => self.expr(expr),
            _ => todo!("{item:?}"),
        }
    }

    fn function(&mut self, func: &Function) -> Result<()> {
        let function_start = self.builder.create_label();
        let function_end = self.builder.create_label();

        self.builder.insert(Instr::CreateFunction { stack_size: func.stack_size as u16 });
        self.builder.insert(Instr::Store(func.ident.local as u32));
        self.builder.insert(Instr::Jump(function_end));
        self.builder.insert_label(function_start);

        // self.scopes.push(FunctionScope::new(ret.clone()));
        self.block(&func.body)?;
        // let num_scope_vars = self.scopes.last().unwrap().variables.len();
        // TODO: Remove extra space for ZSTs
        // self.scopes.pop().unwrap();

        let ret = Ty::Var(func.ret).sub(&self.subs);
        if ret == Ty::null() {
            self.builder.insert(Instr::Ret);
        } else {
            // FIXME: Instead produce a compile error when this is possible
            self.builder.insert(Instr::Abort);
        }

        self.builder.insert_label(function_end);
        Ok(())
    }

    fn expr(&mut self, expr: &Expr) -> Result<()> {
        match expr.kind {
            ExprKind::Binary { ref exprs, op } => self.binary_expr(op, &exprs[0], &exprs[1])?,
            ExprKind::Int(int) => self.builder.insert(Instr::LoadInt(int)),
            ref kind => todo!("{kind:?}"),
        }
        Ok(())
    }

    fn binary_expr(&mut self, op: BinOp, lhs: &Expr, rhs: &Expr) -> Result<()> {
        match op {
            BinOp::Or | BinOp::And => self.logical_bool_expr(op, lhs, rhs)?,
            _ => {}
        }
        self.expr(lhs)?;
        self.expr(rhs)?;
        assert_eq!(self.ty(&lhs.ty), self.ty(&rhs.ty));

        match op {
            BinOp::Add => self.builder.insert(Instr::AddInt),
            _ => todo!("{op:?}"),
        }
        Ok(())
    }

    fn logical_bool_expr(&mut self, op: BinOp, lhs: &Expr, rhs: &Expr) -> Result<()> {
        _ = op;
        _ = lhs;
        _ = rhs;
        todo!()
    }

    fn ty(&self, ty: &Ty) -> Ty {
        ty.sub(&self.subs)
    }
}
