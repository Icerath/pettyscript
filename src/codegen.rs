use miette::Result;

use crate::{
    builtints::MethodBuiltin,
    bytecode::{BytecodeBuilder, Instr},
    mir::*,
    parser::{BinOp, UnaryOp},
    typck::{Substitutions, Ty, TyCon, TyKind},
};

pub fn codegen(block: &Block, subs: Substitutions, main_fn: Option<Offset>) -> Result<Vec<u8>> {
    let mut codegen = Codegen { subs, ..Default::default() };
    codegen.block(block)?;
    // TODO: Actually count this.
    codegen.builder.set_global_stack_size(64);
    if let Some(offset) = main_fn {
        codegen.load(offset);
        codegen.builder.insert(Instr::FnCall);
    }
    Ok(codegen.builder.finish())
}

#[derive(Default)]
struct Codegen {
    subs: Substitutions,
    builder: BytecodeBuilder,
    continue_label: Option<u32>,
    break_label: Option<u32>,
}

impl Codegen {
    fn ty(&mut self, ty: &Ty) -> TyCon {
        let Ty::Con(tycon) = ty.sub(&self.subs) else { panic!() };
        tycon
    }

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
            Item::Loop(block) => self.loop_(block),
            Item::Continue => self.continue_(),
            Item::Break => self.break_(),
            Item::Return(ret) => self.return_(ret),
            Item::Expr(expr) => {
                self.expr(expr)?;
                if self.ty(&expr.ty).kind != TyKind::null() {
                    self.builder.insert(Instr::Pop);
                }
                Ok(())
            }
        }
    }

    fn function(&mut self, func: &Function) -> Result<()> {
        let function_start = self.builder.create_label();
        let function_end = self.builder.create_label();

        self.builder.insert(Instr::CreateFunction { stack_size: func.stack_size as u16 });
        self.store(func.ident.offset);
        self.builder.insert(Instr::Jump(function_end));
        self.builder.insert_label(function_start);

        for param in func.params.iter().rev() {
            self.store(param.offset);
        }

        // self.scopes.push(FunctionScope::new(ret.clone()));
        self.block(&func.body)?;
        // let num_scope_vars = self.scopes.last().unwrap().variables.len();
        // TODO: Remove extra space for ZSTs
        // self.scopes.pop().unwrap();

        if self.ty(&func.ret).kind == TyKind::null() {
            self.builder.insert(Instr::Ret);
        } else {
            // FIXME: Instead produce a compile error when this is possible
            self.builder.insert(Instr::Abort);
        }

        self.builder.insert_label(function_end);
        Ok(())
    }

    fn assign(&mut self, assign: &Assign) -> Result<()> {
        if assign.segments.is_empty() {
            self.expr(&assign.expr)?;
            self.store(assign.root.offset);
            return Ok(());
        }
        self.load(assign.root.offset);
        let (last, segments) = assign.segments.split_last().unwrap();
        for segment in segments {
            match segment {
                AssignSegment::Field(field) => self.builder.insert(Instr::LoadField(*field)),
                AssignSegment::Index(_) => todo!(),
            }
        }
        self.expr(&assign.expr)?;
        match last {
            AssignSegment::Field(field) => {
                self.builder.insert(Instr::StoreField(*field));
                self.builder.insert(Instr::Pop);
            }
            AssignSegment::Index(_) => todo!(),
        }
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
            self.builder.insert(Instr::Jump(end_label));
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
        let iter_op = match self.ty(&for_loop.iter.ty).kind {
            TyKind::Named("range" | "range_inclusive") => Instr::IterRange,
            ty => panic!("{ty:?}"),
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

        self.builder.insert(Instr::Pop);

        self.continue_label = prev_continue;
        self.break_label = prev_break;
        Ok(())
    }

    fn loop_(&mut self, block: &Block) -> Result<()> {
        let start_label = self.builder.create_label();
        let end_label = self.builder.create_label();

        let prev_continue = self.continue_label.replace(start_label);
        let prev_break = self.break_label.replace(end_label);

        self.builder.insert_label(start_label);
        self.block(block)?;
        self.builder.insert(Instr::Jump(start_label));
        self.builder.insert_label(end_label);

        self.continue_label = prev_continue;
        self.break_label = prev_break;

        Ok(())
    }

    fn continue_(&mut self) -> Result<()> {
        self.builder.insert(Instr::Jump(self.continue_label.unwrap()));
        Ok(())
    }

    fn break_(&mut self) -> Result<()> {
        self.builder.insert(Instr::Jump(self.break_label.unwrap()));
        Ok(())
    }

    fn return_(&mut self, ret: &Return) -> Result<()> {
        for _ in 0..ret.pops {
            self.builder.insert(Instr::Pop);
        }
        if let Some(expr) = &ret.expr {
            self.expr(expr)?;
        }
        self.builder.insert(Instr::Ret);
        Ok(())
    }

    fn expr(&mut self, expr: &Expr) -> Result<()> {
        self.expr_kind(&expr.kind)
    }

    fn expr_kind(&mut self, expr: &ExprKind) -> Result<()> {
        match &expr {
            ExprKind::StructInit { fields } => self.struct_init(fields)?,
            ExprKind::FieldAccess { expr, field } => self.field_access(expr, field)?,
            ExprKind::EnumVariant { tag } => self.builder.insert(Instr::LoadVariant { tag: *tag }),
            ExprKind::MethodCall { expr, method, args } => self.method_call(expr, method, args)?,
            ExprKind::FnCall { expr, args } => self.fn_call(expr, args)?,
            ExprKind::Index { expr, index } => self.index(expr, index)?,
            ExprKind::Unary { expr, op } => self.unary_expr(*op, expr)?,
            ExprKind::Binary { exprs, op } => self.binary_expr(*op, &exprs[0], &exprs[1])?,
            ExprKind::Bool(bool) => self.builder.insert(Instr::LoadBool(*bool)),
            ExprKind::Int(int) => self.builder.insert(Instr::LoadInt(*int)),
            ExprKind::Char(char) => self.builder.insert(Instr::LoadChar(*char)),
            ExprKind::Str(str) => {
                let str_ident = self.builder.insert_string(str);
                self.builder.insert(Instr::LoadString(str_ident));
            }
            ExprKind::Format(expr) => self.format(expr)?,
            ExprKind::Fstr(fstr) => self.fstr(fstr)?,
            ExprKind::Tuple(tuple) => self.array(tuple)?,
            ExprKind::Array(arr) => self.array(arr)?,
            ExprKind::Map(map) => self.map(map)?,
            ExprKind::LoadIdent { offset } => self.load(*offset),
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

    fn field_access(&mut self, expr: &Expr, field: &'static str) -> Result<()> {
        let ty = self.ty(&expr.ty);
        let TyKind::Struct { fields, .. } = &ty.kind else { panic!("Expected `struct` {ty:?}") };
        let field_id = fields.get(field).unwrap().0;
        self.expr(expr)?;
        self.builder.insert(Instr::LoadField(field_id));
        Ok(())
    }

    fn method_call(&mut self, expr: &Expr, method: &str, args: &[Expr]) -> Result<()> {
        use MethodBuiltin as M;
        self.expr(expr)?;

        for expr in args {
            self.expr(expr)?;
        }

        let ty = self.ty(&expr.ty);
        let builtin = match (&ty.kind, method) {
            (TyKind::Named("int"), "abs") => M::IntAbs,

            (TyKind::Named("char"), "is_digit") => M::CharIsDigit,
            (TyKind::Named("char"), "is_alphabetic") => M::CharIsAlphabetic,

            (TyKind::Named("str"), "trim") => M::StrTrim,
            (TyKind::Named("str"), "is_digit") => M::StrIsDigit,
            (TyKind::Named("str"), "is_alphabetic") => M::StrIsAlphabetic,
            (TyKind::Named("str"), "starts_with") => M::StrStartsWith,
            (TyKind::Named("str"), "len") => M::StrLen,
            (TyKind::Named("str"), "lines") => M::StrLines,

            (TyKind::Named("array"), "push") => M::ArrayPush,
            (TyKind::Named("array"), "pop") => M::ArrayPop,
            (TyKind::Named("array"), "sort") if ty.generics[0] == Ty::int() => M::ArraySortInt,
            (TyKind::Named("array"), "len") => M::ArrayLen,

            (TyKind::Named("map"), "insert") => M::MapInsert,
            (TyKind::Named("map"), "remove") => M::MapRemove,
            (TyKind::Named("map"), "get") => M::MapGet,
            (TyKind::Named("map"), "contains") => M::MapContains,

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

    fn index(&mut self, expr: &Expr, index: &Expr) -> Result<()> {
        self.expr(expr)?;
        self.expr(index)?;
        let ty = self.ty(&expr.ty).kind;
        let index = self.ty(&index.ty).kind;
        if ty == TyKind::str() {
            if index == TyKind::int() {
                self.builder.insert(Instr::StringIndex);
            } else if index == TyKind::range() {
                self.builder.insert(Instr::StringSliceRange);
            } else {
                panic!()
            }
        } else if let TyKind::Named("array") = ty {
            self.builder.insert(Instr::ArrayIndex);
        }
        Ok(())
    }

    fn unary_expr(&mut self, op: UnaryOp, expr: &Expr) -> Result<()> {
        self.expr(expr)?;
        match op {
            UnaryOp::Neg => {
                assert_eq!(self.ty(&expr.ty).kind, TyKind::int());
                self.builder.insert(Instr::Neg);
            }
            UnaryOp::Not => {
                assert_eq!(self.ty(&expr.ty).kind, TyKind::bool());
                self.builder.insert(Instr::Not);
            }
            UnaryOp::EnumTag => {
                let TyKind::Variant { .. } = &self.ty(&expr.ty).kind else { panic!() };
                self.builder.insert(Instr::EnumTag);
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

        match op {
            BinOp::Add => self.builder.insert(Instr::AddInt),
            BinOp::Sub => self.builder.insert(Instr::SubInt),
            BinOp::Mul => self.builder.insert(Instr::MulInt),
            BinOp::Div => self.builder.insert(Instr::DivInt),
            BinOp::Mod => self.builder.insert(Instr::Mod),
            BinOp::Eq => self.builder.insert(Instr::Eq),
            BinOp::Neq => {
                self.builder.insert(Instr::Eq);
                self.builder.insert(Instr::Not);
            }
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

    fn format(&mut self, format: &Expr) -> Result<()> {
        self.expr(format)?;
        self.builder.insert(Instr::BuildFstr { num_segments: 1 });
        Ok(())
    }

    fn fstr(&mut self, fstr: &Fstr) -> Result<()> {
        let mut num_segments = 0;
        for (str, expr) in &fstr.segments {
            if !str.is_empty() {
                let str_ident = self.builder.insert_string(str);
                self.builder.insert(Instr::LoadString(str_ident));
                num_segments += 1;
            }
            self.expr_kind(expr)?;
            num_segments += 1;
        }
        if !fstr.remaining.is_empty() {
            let str_ident = self.builder.insert_string(fstr.remaining);
            self.builder.insert(Instr::LoadString(str_ident));
            num_segments += 1;
        }
        self.builder.insert(Instr::BuildFstr { num_segments });
        Ok(())
    }

    fn array(&mut self, arr: &[Expr]) -> Result<()> {
        arr.iter().try_for_each(|expr| self.expr(expr))?;
        self.builder.insert(Instr::CreateArray { size: arr.len() as u16 });
        Ok(())
    }

    fn map(&mut self, exprs: &[[Expr; 2]]) -> Result<()> {
        for [key, value] in exprs {
            self.expr(key)?;
            self.expr(value)?;
        }
        self.builder.insert(Instr::CreateMap { num_keys: exprs.len().try_into().unwrap() });
        Ok(())
    }

    fn load(&mut self, offset: Offset) {
        match offset {
            Offset::Local(offset) => self.builder.insert(Instr::Load(offset)),
            Offset::Global(offset) => self.builder.insert(Instr::LoadGlobal(offset)),
        }
    }

    #[expect(clippy::match_same_arms)]
    fn store(&mut self, offset: Offset) {
        match offset {
            Offset::Local(offset) => self.builder.insert(Instr::Store(offset)),
            // ???
            Offset::Global(offset) => self.builder.insert(Instr::Store(offset)),
        }
    }
}
