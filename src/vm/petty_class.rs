use std::{collections::BTreeMap, fmt};

use crate::{
    ast::Node,
    rc_str::RcStr,
    slim_rc::Rc,
    vm::builtins::{function_template::SingleTemplate, PtyStr},
};

use super::{
    builtins::{self, PtyNull},
    core::Vm,
    function_args::FuncArgs,
    object::{PettyObject, PettyObjectType},
    petty_function::PettyFunction,
};

#[derive(Clone)]
pub struct PettyClassInstance {
    pub fields: BTreeMap<RcStr, PettyObject>,
}
pub struct PettyClass {
    pub fields: Rc<[RcStr]>,
    pub methods: Rc<[Node]>,
}
impl PettyClass {
    pub fn new(fields: Rc<[RcStr]>, methods: Rc<[Node]>) -> Self {
        Self { fields, methods }
    }
}
impl PettyClassInstance {
    pub fn new(fields: BTreeMap<RcStr, PettyObject>) -> Self {
        Self { fields }
    }
}
impl PettyObjectType for PettyClassInstance {
    fn get_item(&self, vm: &mut Vm, this: PettyObject, str: &str) -> PettyObject {
        if let Some(item) = self.fields.get(str) {
            return item.clone();
        }
        match str {
            "__repr__" => SingleTemplate(|this: &Self| {
                PtyStr(format!("Class Instance at {:?}", this as *const Self).into())
            })
            .into(),
            _ => todo!("{str}"),
        }
    }
    fn call(&self, vm: &mut Vm, this: PettyObject, mut args: FuncArgs) -> PettyObject {
        let function = self.get_item(vm, this.clone(), "__call__");
        args.0.push(this.clone());
        function.call(vm, this, args)
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

impl PettyObjectType for PettyClass {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn call(&self, vm: &mut Vm, this: PettyObject, args: FuncArgs) -> PettyObject {
        if self.fields.len() != args.0.len() {
            todo!(
                "Expected {} Arguments got {}",
                self.fields.len(),
                args.0.len()
            );
        }
        let mut fields: BTreeMap<Rc<str>, PettyObject> = self
            .fields
            .iter()
            .cloned()
            .zip(args.0.iter().cloned())
            .collect();
        for function in self.methods.iter().cloned() {
            let Node::FuncDef(name, params, body) = function else {
            unreachable!();
        };
            let function = PettyFunction::new(params, body);
            fields.insert(name, function.into());
        }
        PettyClassInstance::new(fields).into()
    }
    fn get_item(&self, vm: &mut Vm, this: PettyObject, str: &str) -> PettyObject {
        todo!()
    }
}

impl fmt::Display for PettyClassInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Petty Class Instance at {:?}", self as *const Self)
    }
}

impl fmt::Display for PettyClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        builtins::display_class_object(self, f)
    }
}
