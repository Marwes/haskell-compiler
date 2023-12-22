use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    ops::Deref,
    rc::Rc,
};

#[derive(Eq, PartialEq, Clone, Copy, Default, Hash, Debug)]
pub struct InternedStr(usize);

pub struct Interner {
    indexes: HashMap<String, usize>,
    strings: Vec<String>,
}

impl Interner {
    pub fn new() -> Self {
        Self {
            indexes: HashMap::new(),
            strings: vec![],
        }
    }

    pub fn intern(&mut self, s: &str) -> InternedStr {
        match self.indexes.get(s).map(|x| *x) {
            Some(index) => InternedStr(index),
            None => {
                let index = self.strings.len();
                self.indexes.insert(s.to_string(), index);
                self.strings.push(s.to_string());
                InternedStr(index)
            }
        }
    }

    pub fn get_str<'a>(&'a self, InternedStr(i): InternedStr) -> &'a str {
        if i < self.strings.len() {
            &*self.strings[i]
        } else {
            panic!("Invalid InternedStr {:?}", i)
        }
    }
}

///Returns a reference to the interner stored in TLD
pub fn get_local_interner() -> Rc<RefCell<Interner>> {
    thread_local!(static INTERNER: Rc<RefCell<Interner>> = Rc::new(RefCell::new(Interner::new())));
    INTERNER.with(|interner| interner.clone())
}

pub fn intern(s: &str) -> InternedStr {
    let i = get_local_interner();
    let mut i = i.borrow_mut();
    i.intern(s)
}

impl Deref for InternedStr {
    type Target = str;
    fn deref(&self) -> &str {
        self.as_ref()
    }
}

impl AsRef<str> for InternedStr {
    fn as_ref(&self) -> &str {
        let interner = get_local_interner();
        let x = (*interner).borrow_mut();
        let r: &str = x.get_str(*self);
        //The interner is task local and will never remove a string so this is safe
        unsafe { ::std::mem::transmute(r) }
    }
}

impl fmt::Display for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.as_ref())
    }
}
