use std::{
    collections::{
        hash_map::{
            Entry,
            IterMut,
        },
        HashMap,
    },
    hash::Hash,
};

///A map struct which allows for the isizeroduction of different scopes
///Introducing a new scope will make it possible to isizeroduce additional
///variables with names already defined, shadowing the old name
///After exiting a scope the shadowed variable will again be re isizeroduced
pub struct ScopedMap<K, V> {
    ///A hashmap storing a key -> value mapping
    ///Stores a vector of values in which the value at the top is value returned from 'find'
    map: HashMap<K, Vec<V>>,
    ///A vector of scopes, when entering a scope, None is added as a marker
    ///when later exiting a scope, values are removed from the map until the marker is found
    scopes: Vec<Option<K>>,
}

#[allow(dead_code)]
impl<K, V> ScopedMap<K, V>
where
    K: Eq + Hash + Clone,
{
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            scopes: vec![],
        }
    }
    ///Introduces a new scope
    pub fn enter_scope(&mut self) {
        self.scopes.push(None);
    }
    ///Exits the current scope, removing anything inserted since the
    ///matching enter_scope call
    pub fn exit_scope(&mut self) {
        loop {
            match self.scopes.pop() {
                Some(Some(key)) => {
                    self.map.get_mut(&key).map(|x| x.pop());
                }
                _ => break,
            }
        }
    }
    ///Removes a previusly inserted value from the map.
    pub fn remove(&mut self, k: &K) -> bool {
        match self.map.get_mut(k).map(|x| x.pop()) {
            Some(..) => {
                let mut i = self.scopes.len() as isize - 1;
                while i >= 0 {
                    if self.scopes[i as usize].as_ref().map_or(false, |x| x == k) {
                        self.scopes.remove(i as usize);
                    }
                    i -= 1;
                }
                true
            }
            None => false,
        }
    }

    ///Returns true if the key has a value declared in the last declared scope
    pub fn in_current_scope(&self, k: &K) -> bool {
        for n in self.scopes.iter().rev() {
            match *n {
                Some(ref name) if name == k => return true,
                None => break,
                _ => (),
            }
        }
        false
    }
    ///Returns an iterator of the (key, values) pairs inserted in the map
    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, K, Vec<V>> {
        self.map.iter_mut()
    }

    ///Returns a reference to the last inserted value corresponding to the key
    pub fn find<'a>(&'a self, k: &K) -> Option<&'a V> {
        self.map.get(k).and_then(|x| x.last())
    }

    ///Returns the number of elements in the container.
    ///Shadowed elements are not counted
    pub fn len(&self) -> usize {
        self.map.len()
    }

    ///Removes all elements
    pub fn clear(&mut self) {
        self.map.clear();
        self.scopes.clear();
    }

    ///Swaps the value stored at key, or inserts it if it is not present
    pub fn swap(&mut self, k: K, v: V) -> Option<V> {
        let vec = match self.map.entry(k.clone()) {
            Entry::Vacant(entry) => entry.insert(vec![]),
            Entry::Occupied(entry) => entry.into_mut(),
        };
        if !vec.is_empty() {
            let r = vec.pop();
            vec.push(v);
            r
        } else {
            vec.push(v);
            self.scopes.push(Some(k));
            None
        }
    }
    pub fn pop(&mut self, k: &K) -> Option<V> {
        match self.map.get_mut(k).and_then(|x| x.pop()) {
            Some(v) => {
                let mut i = self.scopes.len() as isize - 1;
                while i >= 0 {
                    if self.scopes[i as usize].as_ref().map_or(false, |x| x == k) {
                        self.scopes.remove(i as usize);
                    }
                    i -= 1;
                }
                Some(v)
            }
            None => None,
        }
    }
    pub fn find_mut<'a>(&'a mut self, key: &K) -> Option<&'a mut V> {
        self.map.get_mut(key).and_then(|x| x.last_mut())
    }
    pub fn insert(&mut self, k: K, v: V) -> bool {
        let vec = match self.map.entry(k.clone()) {
            Entry::Vacant(entry) => entry.insert(vec![]),
            Entry::Occupied(entry) => entry.into_mut(),
        };
        vec.push(v);
        self.scopes.push(Some(k));
        vec.len() == 1
    }
}

#[cfg(test)]
mod tests {
    use crate::scoped_map::ScopedMap;
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
