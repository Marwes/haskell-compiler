extern crate collections;
use collections::HashMap;
use collections::hashmap::MutEntries;
use std::hash::Hash;
use std::hash::sip::SipHasher;

pub struct ScopedMap<K, V> {
    map: HashMap<K, Vec<V>, SipHasher>,
    scopes: Vec<Option<K>>
}

#[allow(dead_code)]
impl <K: TotalEq + Hash + Clone, V> ScopedMap<K, V> {
    pub fn new() -> ScopedMap<K, V> {
        ScopedMap { map: HashMap::new(), scopes: Vec::new() }
    }
    pub fn enter_scope(&mut self) {
        self.scopes.push(None);
    }
    pub fn exit_scope(&mut self) {
        loop {
            match self.scopes.pop() {
                Some(Some(key)) => { self.map.find_mut(&key).map(|x| x.pop()); }
                _ => break
            }
        }
    }

    pub fn remove(&mut self, k: &K) -> bool {
        match self.map.find_mut(k).map(|x| x.pop()) {
            Some(..) => {
                let mut i = self.scopes.len() as int - 1;
                while i >= 0 {
                    if self.scopes.get(i as uint).as_ref().map_or(false, |x| x == k) {
                        self.scopes.remove(i as uint);
                    }
                    i -= 1;
                }
                true
            }
            None => false
        }
    }

    pub fn find_equiv<'a, Q: Hash + Equiv<K>>(&'a self, k: &Q) -> Option<&'a V> {
        self.map.find_equiv(k).and_then(|x| x.last())
    }

    pub fn mut_iter<'a>(&'a mut self) -> MutEntries<'a, K, Vec<V>> {
        self.map.mut_iter()
    }
}

impl <K: TotalEq + Hash, V> Map<K, V> for ScopedMap<K, V> {
    fn find<'a>(&'a self, k: &K) -> Option<&'a V> {
        self.map.find(k).and_then(|x| x.last())
    }
}
impl <K: TotalEq + Hash, V> Container for ScopedMap<K, V> {
    fn len(&self) -> uint { self.map.len() }
}
impl <K: TotalEq + Hash, V> Mutable for ScopedMap<K, V> {
    fn clear(&mut self) {
        self.map.clear();
        self.scopes.clear();
    }
}
impl <K: TotalEq + Hash + Clone, V> MutableMap<K, V> for ScopedMap<K, V> {
    fn swap(&mut self, k: K, v: V) -> Option<V> {
        let vec = self.map.find_or_insert(k.clone(), Vec::new());
        if vec.len() != 0 {
            let r  = vec.pop();
            vec.push(v);
            r
        }
        else {
            vec.push(v);
            self.scopes.push(Some(k));
            None
        }
    }
    fn pop(&mut self, k: &K) -> Option<V> {
        match self.map.find_mut(k).and_then(|x| x.pop()) {
            Some(v) => {
                let mut i = self.scopes.len() as int - 1;
                while i >= 0 {
                    if self.scopes.get(i as uint).as_ref().map_or(false, |x| x == k) {
                        self.scopes.remove(i as uint);
                    }
                    i -= 1;
                }
                Some(v)
            }
            None => None
        }
    }
    fn find_mut<'a>(&'a mut self, key: &K) -> Option<&'a mut V> {
        self.map.find_mut(key).and_then(|x| x.mut_last())
    }
    fn insert(&mut self, k: K, v: V) -> bool {
        let vec = self.map.find_or_insert(k.clone(), Vec::new());
        vec.push(v);
        self.scopes.push(Some(k));
        vec.len() == 1
    }
}

#[cfg(test)]
mod tests {
    use scoped_map::ScopedMap;
    #[test]
    fn test() {
        let mut map = ScopedMap::new();
        map.insert("a", 0);
        map.insert("b", 1);
        map.enter_scope();
        assert_eq!(map.find(&"a"), Some(&0));
        assert_eq!(map.find(&"b"), Some(&1));
        assert_eq!(map.find(&"c"), None);
        map.insert("a", 1);
        map.insert("c", 2);
        assert_eq!(map.find(&"a"), Some(&1));
        assert_eq!(map.find(&"c"), Some(&2));
        map.exit_scope();
        assert_eq!(map.find(&"a"), Some(&0));
        assert_eq!(map.find(&"c"), None);
    }
}
