use collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use std::fmt;

#[deriving(TotalEq, Eq, Clone, Default, Hash)]
pub struct InternedStr(uint);

pub struct Interner {
    indexes: HashMap<~str, uint>,
    strings: Vec<~str>
}

impl Interner {

    pub fn new() -> Interner {
        Interner { indexes: HashMap::new(), strings: Vec::new() }
    }

    pub fn intern(&mut self, s: &str) -> InternedStr {
        match self.indexes.find_equiv(&s).map(|x| *x) {
            Some(index) => InternedStr(index),
            None => {
                let index = self.strings.len();
                self.indexes.insert(s.to_owned(), index);
                self.strings.push(s.to_owned());
                InternedStr(index)
            }
        }
    }

    pub fn get_str<'a>(&'a self, InternedStr(i): InternedStr) -> &'a str {
        if i < self.strings.len() {
            self.strings.get(i).as_slice()
        }
        else {
            fail!("Invalid InternedStr {}", i)
        }
    }
}

pub fn get_local_interner() -> Rc<RefCell<Interner>> {
    local_data_key!(key: Rc<RefCell<Interner>>)
    match ::std::local_data::get(key, |x| x.map(|y| y.clone())) {
        Some(interner) => interner.clone(),
        None => {
            let interner = Rc::new(RefCell::new(Interner::new()));
            ::std::local_data::set(key, interner.clone());
            interner
        }
    }
}

pub fn intern(s: &str) -> InternedStr {
    let i = get_local_interner();
    (*i).borrow_mut().intern(s)
}

impl Str for InternedStr {
    fn as_slice<'a>(&'a self) -> &'a str {
        let interner = get_local_interner();
        let mut x = (*interner).borrow_mut();
        let r: &str = x.get_str(*self);
        //The interner is task local and will never remove a string so this is safe
        unsafe { ::std::cast::transmute(r) }
    }
    fn into_owned(self) -> ~str {
        self.as_slice().into_owned()
    }
}

impl fmt::Show for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f.buf, "{}", self.as_slice())
    }
}
