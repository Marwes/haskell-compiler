use std::collections::HashMap;
use std::default::Default;
use std::fmt;
use std::iter;
use interner::{InternedStr, intern};

#[derive(Clone, Debug, Default, Eq, Hash)]
pub struct TypeConstructor<Ident = InternedStr> {
    pub name : Ident,
    pub kind : Kind
}

impl <Id, Id2> PartialEq<TypeConstructor<Id2>> for TypeConstructor<Id>
    where Id: PartialEq<Id2> {
    fn eq(&self, other: &TypeConstructor<Id2>) -> bool {
        self.name == other.name && self.kind == other.kind
    }
}

pub type VarId = InternedStr;
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct TypeVariable {
    pub id : InternedStr,
    pub kind : Kind,
    pub age: isize
}
#[derive(Clone, Debug, Eq, Hash)]
pub enum Type<Ident = InternedStr> {
    Variable(TypeVariable),
    Constructor(TypeConstructor<Ident>),
    Application(Box<Type<Ident>>, Box<Type<Ident>>),
    Generic(TypeVariable)
}
#[derive(Clone, Debug, Default, Hash)]
pub struct Qualified<T, Ident = InternedStr> {
    pub constraints: Vec<Constraint<Ident>>,
    pub value: T
}
pub fn qualified<Ident>(constraints: Vec<Constraint<Ident>>, typ: Type<Ident>) -> Qualified<Type<Ident>, Ident> {
    Qualified { constraints: constraints, value: typ }
}

impl TypeVariable {
    pub fn new(id : VarId) -> TypeVariable {
        TypeVariable::new_var_kind(id, Kind::Star)
    }
    pub fn new_var_kind(id : VarId, kind: Kind) -> TypeVariable {
        TypeVariable { id : id, kind: kind, age: 0 }
    }
}

impl <Id: fmt::Display + AsRef<str>> Type<Id> {

    ///Creates a new type variable with the specified id
    pub fn new_var(id : VarId) -> Type<Id> {
        Type::new_var_kind(id, Kind::Star)
    }
    ///Creates a new type which is a type variable which takes a number of types as arguments
    ///Gives the typevariable the correct kind arity.
    pub fn new_var_args(id: VarId, types : Vec<Type<Id>>) -> Type<Id> {
        Type::new_type_kind(Type::Variable(TypeVariable { id : id, kind: Kind::Star, age: 0 }), types)
    }
    ///Creates a new type variable with the specified kind
    pub fn new_var_kind(id : VarId, kind: Kind) -> Type<Id> {
        Type::Variable(TypeVariable::new_var_kind(id, kind))
    }
    ///Creates a new type constructor with the specified argument and kind
    pub fn new_op(name : Id, types : Vec<Type<Id>>) -> Type<Id> {
        Type::new_type_kind(Type::Constructor(TypeConstructor { name : name, kind: Kind::Star }), types)
    }
    ///Creates a new type constructor applied to the types and with a specific kind
    pub fn new_op_kind(name : Id, types : Vec<Type<Id>>, kind: Kind) -> Type<Id> {
        let mut result = Type::Constructor(TypeConstructor { name : name, kind: kind });
        for typ in types.into_iter() {
            result = Type::Application(box result, box typ);
        }
        result
    }
    fn new_type_kind(mut result: Type<Id>, types: Vec<Type<Id>>) -> Type<Id> {
        *result.mut_kind() = Kind::new(types.len() as isize + 1);
        for typ in types.into_iter() {
            result = Type::Application(box result, box typ);
        }
        result
    }

    ///Returns a reference to the type variable or fails if it is not a variable
    pub fn var(&self) -> &TypeVariable {
        match self {
            &Type::Variable(ref var) => var,
            _ => panic!("Tried to unwrap {} as a TypeVariable", self)
        }
    }

    ///Returns a reference to the type constructor or fails if it is not a constructor
    #[allow(dead_code)]
    pub fn ctor(&self) -> &TypeConstructor<Id> {
        match self {
            &Type::Constructor(ref op) => op,
            _ => panic!("Tried to unwrap {} as a TypeConstructor", self)
        }
    }

    ///Returns a reference to the the type function or fails if it is not an application
    #[allow(dead_code)]
    pub fn appl(&self) -> &Type<Id> {
        match self {
            &Type::Application(ref lhs, _) => &**lhs,
            _ => panic!("Error: Tried to unwrap {} as TypeApplication", self)
        }
    }
    #[allow(dead_code)]
    ///Returns a reference to the the type argument or fails if it is not an application
    pub fn appr(&self) -> &Type<Id> {
        match self {
            &Type::Application(_, ref rhs) => &**rhs,
            _ => panic!("Error: Tried to unwrap TypeApplication")
        }
    }

    ///Returns the kind of the type
    ///Fails only if the type is a type application with an invalid kind
    pub fn kind(&self) -> &Kind {
        match self {
            &Type::Variable(ref v) => &v.kind,
            &Type::Constructor(ref v) => &v.kind,
            &Type::Application(ref lhs, _) => 
                match lhs.kind() {
                    &Kind::Function(_, ref kind) => &**kind,
                    _ => panic!("Type application must have a kind of Kind::Function, {}", self)
                },
            &Type::Generic(ref v) => &v.kind
        }
    }
    ///Returns a mutable reference to the types kind
    pub fn mut_kind(&mut self) -> &mut Kind {
        match *self {
            Type::Variable(ref mut v) => &mut v.kind,
            Type::Constructor(ref mut v) => &mut v.kind,
            Type::Application(ref mut lhs, _) => 
                match *lhs.mut_kind() {
                    Kind::Function(_, ref mut kind) => &mut **kind,
                    _ => panic!("Type application must have a kind of Kind::Function")
                },
            Type::Generic(ref mut v) => &mut v.kind
        }
    }
}
impl <Id> Type <Id> {
    pub fn map<F, Id2>(self, mut f: F) -> Type<Id2>
        where F: FnMut(Id) -> Id2 {
        self.map_(&mut f)
    }
    fn map_<F, Id2>(self, f: &mut F) -> Type<Id2>
        where F: FnMut(Id) -> Id2 {
        match self {
            Type::Variable(v) => Type::Variable(v),
            Type::Constructor(TypeConstructor { name, kind }) => {
                Type::Constructor(TypeConstructor { name: f(name), kind: kind })
            }
            Type::Application(lhs, rhs) => Type::Application(box lhs.map_(f), box rhs.map_(f)),
            Type::Generic(v) => Type::Generic(v)
        }
    }
}

impl ::std::hash::Hash for TypeVariable {
    #[inline]
    fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
        //Only has the id since the kind should always be the same for two variables
        self.id.hash(state);
    }
}

///Constructs a string which holds the name of an n-tuple
pub fn tuple_name(n: usize) -> String {
    let commas = if n == 0 { 0 } else { n - 1 };
    Some('(').into_iter()
        .chain(iter::repeat(',').take(commas))
        .chain(Some(')').into_iter())
        .collect()
}
///Returns the type of an n-tuple constructor as well as the name of the tuple
pub fn tuple_type(n: usize) -> (String, Type) {
    let mut var_list = Vec::new();
    assert!(n < 26);
    for i in 0..n {
        let c = (('a' as u8) + i as u8) as char;
        let var = TypeVariable::new_var_kind(intern(&c.to_string()), Kind::Star.clone());
        var_list.push(Type::Generic(var));
    }
    let ident = tuple_name(n);
    let mut typ = Type::new_op(intern(&ident), var_list);
    for i in (0..n).rev() {
        let c = (('a' as u8) + i as u8) as char;
        typ = function_type_(Type::Generic(TypeVariable::new(intern(&c.to_string()))), typ);
    }
    (ident, typ)
}
///Constructs a list type which holds elements of type 'typ'
pub fn list_type(typ: Type) -> Type {
    Type::new_op(intern("[]"), vec![typ])
}
///Returns the Type of the Char type
pub fn char_type() -> Type {
    Type::new_op(intern("Char"), vec![])
}
///Returns the type for the Int type
pub fn int_type() -> Type {
    Type::new_op(intern("Int"), vec![])
}
///Returns the type for the Bool type
pub fn bool_type() -> Type {
    Type::new_op(intern("Bool"), vec![])
}
///Returns the type for the Double type
pub fn double_type() -> Type {
    Type::new_op(intern("Double"), vec![])
}
///Creates a function type
pub fn function_type(arg: &Type, result: &Type) -> Type {
    function_type_(arg.clone(), result.clone())
}

///Creates a function type
pub fn function_type_(func : Type, arg : Type) -> Type {
    Type::new_op(intern("->"), vec![func, arg])
}

///Creates a IO type
pub fn io(typ: Type) -> Type {
    Type::new_op(intern("IO"), vec![typ])
}
///Returns the unit type '()'
pub fn unit() -> Type {
    Type::new_op(intern("()"), vec![])
}


#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Constraint<Ident = InternedStr> {
    pub class : Ident,
    pub variables : Vec<TypeVariable>
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    Function(Box<Kind>, Box<Kind>),
    Star
}
impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Kind::Star => write!(f, "*"),
            &Kind::Function(ref lhs, ref rhs) => write!(f, "({} -> {})", *lhs, *rhs)
        }
    }
}

impl Kind {
    pub fn new(v: isize) -> Kind {
        let mut kind = Kind::Star.clone();
        for _ in 1..v {
            kind = Kind::Function(box Kind::Star, box kind);
        }
        kind
    }
}

impl Default for Kind {
    fn default() -> Kind {
        Kind::Star
    }
}

impl <T> Default for Type<T> {
    fn default() -> Type<T> {
        Type::Variable(TypeVariable::new(intern("a")))
    }
}
impl fmt::Display for TypeVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.id)
    }
}
impl <I: fmt::Display> fmt::Display for TypeConstructor<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl <T: fmt::Display, I: fmt::Display + AsRef<str>> fmt::Display for Qualified<T, I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.constraints.len() != 0 {
            try!(write!(f, "("));
        }
        for constraint in &self.constraints {
            try!(write!(f, "{}, ", constraint));
        }
        if self.constraints.len() != 0 {
            write!(f, ") => {}" , self.value)
        }
        else {
            write!(f, "{}" , self.value)
        }
    }
}

#[derive(PartialEq, Copy, Clone, PartialOrd)]
enum Prec_ {
    Top,
    Function,
    Constructor,
}
#[derive(Copy, Clone)]
struct Prec<'a, Id: 'a>(Prec_, &'a Type<Id>);

///If the type is a function it returns the type of the argument and the result type,
///otherwise it returns None
pub fn try_get_function<'a, Id: AsRef<str>>(typ: &'a Type<Id>) -> Option<(&'a Type<Id>, &'a Type<Id>)> {
    match *typ {
        Type::Application(ref xx, ref result) => {
            match **xx {
                Type::Application(ref xx, ref arg) => {
                    match **xx {
                        Type::Constructor(ref op) if "->" == op.name.as_ref() => {
                            Some((&**arg, &**result))
                        }
                        _ => None
                    }
                }
                _ => None
            }
        }
        _ => None
    }
}

impl <'a, Id: fmt::Display + AsRef<str>> fmt::Display for Prec<'a, Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Prec(p, t) = *self;
        match *t {
            Type::Variable(ref var) => write!(f, "{}", *var),
            Type::Constructor(ref op) => write!(f, "{}", *op),
            Type::Generic(ref var) => write!(f, "\\#{}", *var),
            Type::Application(ref lhs, ref rhs) => {
                match try_get_function(t) {
                    Some((arg, result)) => {
                        if p >= Prec_::Function {
                            write!(f, "({} -> {})", *arg, result)
                        }
                        else {
                            write!(f, "{} -> {}", Prec(Prec_::Function, arg), result)
                        }
                    }
                    None => {
                        match **lhs {
                            Type::Constructor(ref op) if "[]" == op.name.as_ref() => {
                                write!(f, "[{}]", rhs)
                            }
                            _ => {
                                if p >= Prec_::Constructor {
                                    write!(f, "({} {})", Prec(Prec_::Function, &**lhs), Prec(Prec_::Constructor, &**rhs))
                                }
                                else {
                                    write!(f, "{} {}", Prec(Prec_::Function, &**lhs), Prec(Prec_::Constructor, &**rhs))
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

impl <I: fmt::Display + AsRef<str>> fmt::Display for Type<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", Prec(Prec_::Top, self))
    }
}
impl <I: fmt::Display> fmt::Display for Constraint<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{}", self.class));
        for var in self.variables.iter() {
            try!(write!(f, " {}", *var));
        }
        Ok(())
    }
}
fn type_eq<'a, Id, Id2>(mapping: &mut HashMap<&'a TypeVariable, &'a TypeVariable>, lhs: &'a Type<Id>, rhs: &'a Type<Id2>) -> bool
    where Id: PartialEq<Id2> {
    match (lhs, rhs) {
        (&Type::Constructor(ref l), &Type::Constructor(ref r)) => l.name == r.name,
        (&Type::Variable(ref r), &Type::Variable(ref l)) => var_eq(mapping, r, l),
        (&Type::Application(ref lhs1, ref rhs1), &Type::Application(ref lhs2, ref rhs2)) => {
            type_eq(mapping, &**lhs1, &**lhs2) && type_eq(mapping, &**rhs1, &**rhs2)
        }
        _ => false
    }
}

fn var_eq<'a>(mapping: &mut HashMap<&'a TypeVariable, &'a TypeVariable>, l: &'a TypeVariable, r: &'a TypeVariable) -> bool {
    match mapping.get(&l) {
        Some(x) => return x.id == r.id,
        None => ()
    }
    mapping.insert(l, r);
    true
}

impl <I : PartialEq, U: PartialEq> PartialEq for Qualified<Type<I>, U> {
    fn eq(&self, other: &Qualified<Type<I>, U>) -> bool {
        let mut mapping = HashMap::new();
        self.constraints.iter()
            .zip(other.constraints.iter())
            .all(|(l, r)| l.class == r.class && var_eq(&mut mapping, &l.variables[0], &r.variables[0]))
        && type_eq(&mut mapping, &self.value, &other.value)
    }
}
impl <I: Eq, U: Eq> Eq for Qualified<Type<I>, U> { }

impl <Id, Id2> PartialEq<Type<Id2>> for Type<Id>
    where Id: PartialEq<Id2> {
    ///Compares two types, treating two type variables as equal as long as they always and only appear at the same place
    ///a -> b == c -> d
    ///a -> b != c -> c
    fn eq(&self, other: &Type<Id2>) -> bool {
        let mut mapping = HashMap::new();
        type_eq(&mut mapping, self, other)
    }
}

pub fn extract_applied_type<Id>(typ: &Type<Id>) -> &Type<Id> {
    match *typ {
        Type::Application(ref lhs, _) => extract_applied_type(&**lhs),
        _ => typ
    }
}
