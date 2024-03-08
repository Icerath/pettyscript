use crate::prelude::*;

pub fn print(vm: &Vm, args: FnArgs) -> PettyObject {
    for arg in args.slice {
        match arg.get(vm, "__repr__").call(vm, FnArgs::new(&[arg.clone()])) {
            PettyObject::PtyStr(str) => print!("{str} "),
            _ => unreachable!("__repr__ Should always return a str"),
        }
    }
    println!();
    NULL
}
