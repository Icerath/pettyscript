use std::sync::RwLock;

use rustc_hash::{FxBuildHasher, FxHashSet};

static MAP: RwLock<FxHashSet<&'static str>> = RwLock::new(FxHashSet::with_hasher(FxBuildHasher));

pub fn intern(str: &str) -> &'static str {
    if let Some(istr) = MAP.read().unwrap().get(str) {
        return istr;
    }
    insert(str)
}

#[cold]
fn insert(str: &str) -> &'static str {
    let mut cache = MAP.write().unwrap();
    if let Some(istr) = cache.get(str) {
        return istr;
    }
    let istr = str.to_owned().leak();
    cache.insert(istr);
    istr
}
