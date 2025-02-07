use miette::Result;

use crate::{
    builtints::MethodBuiltin,
    bytecode::{BytecodeBuilder, Instr},
    hir::*,
    parser::{BinOp, UnaryOp},
    typck::{Substitutions, Ty, TyKind},
};

pub fn codegen(block: &Block, subs: Substitutions) -> Result<Vec<u8>> {
    let mut codegen = Codegen { subs, ..Default::default() };
    codegen.block(block)?;
    // TODO: Actually count this.
    codegen.builder.set_global_stack_size(64);
    if let Some(offset) = codegen.main_fn {
        codegen.load(offset);
        codegen.builder.insert(Instr::FnCall);
    }
    Ok(codegen.builder.finish())
}

#[derive(Default)]
struct Codegen {
    subs: Substitutions,
    builder: BytecodeBuilder,
    main_fn: Option<Offset>,
    continue_label: Option<u32>,
    break_label: Option<u32>,
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
            Item::Assign(assign) => self.assign(assign),
            Item::IfChain(if_chain) => self.if_chain(if_chain),
            Item::ForLoop(for_loop) => self.for_loop(for_loop),
            Item::Expr(expr) => {
                self.expr(expr)?;
                if self.ty(&expr.ty) != Ty::null() {
                    self.builder.insert(Instr::Pop);
                }
                Ok(())
            }
            _ => todo!("{item:?}"),
        }
    }

    fn function(&mut self, func: &Function) -> Result<()> {
        let function_start = self.builder.create_label();
        let function_end = self.builder.create_label();

        if func.name == "main" {
            self.main_fn = Some(func.ident.offset);
        }
        self.builder.insert(Instr::CreateFunction { stack_size: func.stack_size as u16 });
        self.store(func.ident.offset);
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

    fn assign(&mut self, assign: &Assign) -> Result<()> {
        self.expr(&assign.expr)?;
        self.store(assign.root.offset);
        Ok(())
    }

    fn if_chain(&mut self, if_chain: &IfChain) -> Result<()> {
        let end_label = self.builder.create_label();
        let mut next = self.builder.create_label();
        for (condition, block) in &if_chain.chain {
            self.builder.insert_label(next);
            next = self.builder.create_label();
            self.expr(condition)?;
            self.builder.insert(Instr::CJump(next));
            self.block(block)?;
        }
        self.builder.insert_label(next);
        self.block(&if_chain.end)?;
        self.builder.insert_label(end_label);
        Ok(())
    }

    fn for_loop(&mut self, for_loop: &ForLoop) -> Result<()> {
        let start_label = self.builder.create_label();
        let end_label = self.builder.create_label();

        let prev_continue = self.continue_label.replace(start_label);
        let prev_break = self.break_label.replace(end_label);

        self.expr(&for_loop.iter)?;

        self.builder.insert_label(start_label);
        let Ty::Con(ty) = for_loop.iter.ty.sub(&self.subs) else { panic!() };
        let iter_op = match ty.kind {
            TyKind::Named("range") => Instr::IterRange,
            TyKind::Named("range_inclusive") => Instr::IterRangeInclusive,
            typ => panic!("{typ:?}"),
        };
        self.builder.insert(iter_op);
        self.builder.insert(Instr::CJump(end_label));

        if let Some(ident) = &for_loop.ident {
            self.store(ident.offset);
        } else {
            self.builder.insert(Instr::Pop);
        }

        self.block(&for_loop.body)?;

        self.builder.insert(Instr::Jump(start_label));
        self.builder.insert_label(end_label);

        self.continue_label = prev_continue;
        self.break_label = prev_break;
        Ok(())
    }

    fn expr(&mut self, expr: &Expr) -> Result<()> {
        match &expr.kind {
            ExprKind::StructInit { fields, .. } => self.struct_init(fields)?,
            ExprKind::FieldAccess { expr, field } => self.field_access(expr, field)?,
            ExprKind::MethodCall { expr, method, args } => self.method_call(expr, method, args)?,
            ExprKind::FnCall { expr, args } => self.fn_call(expr, args)?,
            ExprKind::Unary { expr, op } => self.unary_expr(*op, expr)?,
            ExprKind::Binary { exprs, op } => self.binary_expr(*op, &exprs[0], &exprs[1])?,
            ExprKind::Bool(bool) => self.builder.insert(Instr::LoadBool(*bool)),
            ExprKind::Int(int) => self.builder.insert(Instr::LoadInt(*int)),
            ExprKind::Str(str) => {
                let [ptr, len] = self.builder.insert_string(str);
                self.builder.insert(Instr::LoadString { ptr, len });
            }
            ExprKind::Fstr(fstr) => self.fstr(fstr)?,
            ExprKind::Array(arr) => self.array(arr)?,
            ExprKind::Map(map) => self.map(map)?,
            ExprKind::Ident(ident) => self.load(ident.offset),
            kind => todo!("{kind:?}"),
        }
        Ok(())
    }

    fn struct_init(&mut self, fields: &[(u32, Expr)]) -> Result<()> {
        self.builder.insert(Instr::CreateStruct { size: fields.len() as u32 });
        for (id, expr) in fields {
            self.expr(expr)?;
            self.builder.insert(Instr::StoreField(*id));
        }
        Ok(())
    }

    fn field_access(&mut self, expr: &Expr, field: &str) -> Result<()> {
        let ty = &expr.ty.sub(&self.subs);
        let Ty::Con(tycon) = ty else { panic!("Expected `struct` {ty:?}") };
        let TyKind::Struct { fields, .. } = &tycon.kind else {
            panic!("Expected `struct` {tycon:?}")
        };
        let field_id = fields.get(field).unwrap().0;
        self.expr(expr)?;
        self.builder.insert(Instr::LoadField(field_id));
        Ok(())
    }

    fn method_call(&mut self, expr: &Expr, method: &str, args: &[Expr]) -> Result<()> {
        use MethodBuiltin as M;
        self.expr(expr)?;
        let Ty::Con(tycon) = expr.ty.sub(&self.subs) else { panic!() };
        for expr in args {
            self.expr(expr)?;
        }
        let builtin = match (&tycon.kind, method) {
            (TyKind::Named("int"), "abs") => M::IntAbs,

            (TyKind::Named("char"), "is_digit") => M::CharIsDigit,
            (TyKind::Named("char"), "is_alphabetic") => M::CharIsDigit,

            (TyKind::Named("str"), "trim") => M::StrTrim,
            (TyKind::Named("str"), "is_digit") => M::StrTrim,
            (TyKind::Named("str"), "is_alphabetic") => M::StrIsAlphabetic,
            (TyKind::Named("str"), "starts_with") => M::StrIsAlphabetic,

            (TyKind::Named("array"), "push") => M::ArrayPush,
            (TyKind::Named("array"), "pop") => M::ArrayPop,
            (TyKind::Named("array"), "sort") if tycon.generics[0] == Ty::int() => M::ArraySortInt,

            (TyKind::Named("map"), "insert") => M::MapInsert,
            (TyKind::Named("map"), "remove") => M::MapRemove,
            (TyKind::Named("map"), "get") => M::MapGet,

            kind => todo!("{kind:?}"),
        };
        self.builder.insert(Instr::CallBuiltinMethod(builtin));
        Ok(())
    }

    fn fn_call(&mut self, expr: &Expr, args: &[Expr]) -> Result<()> {
        for arg in args {
            self.expr(arg)?;
        }
        self.expr(expr)?;
        self.builder.insert(Instr::FnCall);
        Ok(())
    }

    fn unary_expr(&mut self, op: UnaryOp, expr: &Expr) -> Result<()> {
        self.expr(expr)?;
        match op {
            UnaryOp::Neg => {
                assert_eq!(expr.ty.sub(&self.subs), Ty::int());
                self.builder.insert(Instr::Neg);
            }
            UnaryOp::Not => {
                assert_eq!(expr.ty.sub(&self.subs), Ty::bool());
                self.builder.insert(Instr::Not);
            }
        }
        Ok(())
    }

    fn binary_expr(&mut self, op: BinOp, lhs: &Expr, rhs: &Expr) -> Result<()> {
        match op {
            BinOp::Or | BinOp::And => return self.logical_bool_expr(op, lhs, rhs),
            _ => {}
        }
        self.expr(lhs)?;
        self.expr(rhs)?;
        assert_eq!(self.ty(&lhs.ty), self.ty(&rhs.ty));

        match op {
            BinOp::Add => self.builder.insert(Instr::AddInt),
            BinOp::Mod => self.builder.insert(Instr::Mod),
            BinOp::Eq => self.builder.insert(Instr::Eq),
            BinOp::Less => self.builder.insert(Instr::Less),
            BinOp::Greater => self.builder.insert(Instr::Greater),
            BinOp::Range => self.builder.insert(Instr::Range),
            BinOp::RangeInclusive => self.builder.insert(Instr::RangeInclusive),
            _ => todo!("{op:?}"),
        }
        Ok(())
    }

    fn logical_bool_expr(&mut self, op: BinOp, lhs: &Expr, rhs: &Expr) -> Result<()> {
        let end_label = self.builder.create_label();
        self.expr(lhs)?;
        self.builder.insert(Instr::Dup);
        if op == BinOp::Or {
            self.builder.insert(Instr::Not);
        };
        self.builder.insert(Instr::CJump(end_label));
        self.builder.insert(Instr::Pop);
        self.expr(rhs)?;
        self.builder.insert_label(end_label);
        Ok(())
    }

    fn fstr(&mut self, fstr: &Fstr) -> Result<()> {
        let mut num_segments = 0;
        for (str, expr) in &fstr.segments {
            if !str.is_empty() {
                let [ptr, len] = self.builder.insert_string(str);
                self.builder.insert(Instr::LoadString { ptr, len });
                num_segments += 1;
            }
            self.expr(expr)?;
            num_segments += 1;
        }
        if !fstr.remaining.is_empty() {
            let [ptr, len] = self.builder.insert_string(fstr.remaining);
            self.builder.insert(Instr::LoadString { ptr, len });
            num_segments += 1;
        }
        self.builder.insert(Instr::BuildFstr { num_segments });
        Ok(())
    }

    fn array(&mut self, arr: &[Expr]) -> Result<()> {
        self.builder.insert(Instr::CreateArray);
        for expr in arr {
            self.expr(expr)?;
            self.builder.insert(Instr::ArrayPush);
        }
        Ok(())
    }

    fn map(&mut self, exprs: &[[Expr; 2]]) -> Result<()> {
        self.builder.insert(Instr::CreateMap);
        for [key, value] in exprs {
            self.expr(key)?;
            self.expr(value)?;
            self.builder.insert(Instr::InsertMap);
        }
        Ok(())
    }

    fn load(&mut self, offset: Offset) {
        match offset {
            Offset::Local(offset) => self.builder.insert(Instr::Load(offset)),
            Offset::Global(offset) => self.builder.insert(Instr::LoadGlobal(offset)),
        }
    }

    fn store(&mut self, offset: Offset) {
        match offset {
            Offset::Local(offset) => self.builder.insert(Instr::Store(offset)),
            // ???
            Offset::Global(offset) => self.builder.insert(Instr::Store(offset)),
        }
    }

    fn ty(&self, ty: &Ty) -> Ty {
        ty.sub(&self.subs)
    }
}
