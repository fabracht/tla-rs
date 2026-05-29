use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

thread_local! {
    static NAMES: RefCell<HashMap<Box<str>, Arc<str>>> = RefCell::new(HashMap::new());
    static PRIMED: RefCell<HashMap<Box<str>, Arc<str>>> = RefCell::new(HashMap::new());
}

pub fn intern(s: &str) -> Arc<str> {
    NAMES.with(|m| {
        if let Some(existing) = m.borrow().get(s) {
            return existing.clone();
        }
        let interned: Arc<str> = Arc::from(s);
        m.borrow_mut().insert(Box::from(s), interned.clone());
        interned
    })
}

pub fn primed_name(base: &str) -> Arc<str> {
    PRIMED.with(|m| {
        if let Some(existing) = m.borrow().get(base) {
            return existing.clone();
        }
        let interned: Arc<str> = Arc::from(format!("{}'", base));
        m.borrow_mut().insert(Box::from(base), interned.clone());
        interned
    })
}
