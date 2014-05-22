use collections::HashMap;

pub struct InternedStr(uint);

pub struct Interner {
    indexes: HashMap<~str, uint>,
    strings: Vec<~str>
}

impl Interner {

    pub fn new() -> Interner {
        Interner { indexes: HashMap::new(), strings: Vec::new() }
    }

    pub fn intern(&mut self, s: ~str) -> InternedStr {
        match self.indexes.find(&s).map(|x| *x) {
            Some(index) => InternedStr(index),
            None => {
                let index = self.strings.len();
                self.indexes.insert(s.clone(), index);
                self.strings.push(s);
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
