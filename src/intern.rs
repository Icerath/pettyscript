use std::sync::RwLock;

use hashbrown::HashSet;
use rustc_hash::FxBuildHasher;

// FIXME: use std::collection::HashSet when const HashSet::with_hasher is stabilized.
static MAP: RwLock<HashSet<&'static str, FxBuildHasher>> =
    RwLock::new(HashSet::with_hasher(FxBuildHasher));

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
