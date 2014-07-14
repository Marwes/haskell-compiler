use collections::HashMap;
use std::vec::FromVec;
use std::iter::range_step;
use std::default::Default;
use std::fmt;
use interner::{InternedStr, intern};

#[deriving(Clone, Default, PartialEq, Eq, Hash)]
pub struct TypeConstructor {
    pub name : InternedStr,
    pub kind : Kind
}

pub type VarId = InternedStr;
#[deriving(Clone, PartialEq, Eq, Default)]
pub struct TypeVariable {
    pub id : InternedStr,
    pub kind : Kind,
    pub age: int
}
#[deriving(Clone, Eq, Hash)]
pub enum Type {
    TypeVariable(TypeVariable),
    TypeConstructor(TypeConstructor),
    TypeApplication(Box<Type>, Box<Type>),
    Generic(TypeVariable)
}
#[deriving(Clone, Default, Hash)]
pub struct Qualified<T> {
    pub constraints: ~[Constraint],
    pub value: T
}
pub fn qualified(constraints: ~[Constraint], typ: Type) -> Qualified<Type> {
    Qualified { constraints: constraints, value: typ }
}

impl Type {

    ///Creates a new type variable with the specified id
    pub fn new_var(id : VarId) -> Type {
        Type::new_var_kind(id, StarKind)
    }
    ///Creates a new type which is a type variable which takes a number of types as arguments
    ///Gives the typevariable the correct kind arity.
    pub fn new_var_args(id: VarId, types : ~[Type]) -> Type {
        Type::new_type_kind(TypeVariable(TypeVariable { id : id, kind: StarKind, age: 0 }), types)
    }
    ///Creates a new type variable with the specified kind
    pub fn new_var_kind(id : VarId, kind: Kind) -> Type {
        TypeVariable(TypeVariable { id : id, kind: kind, age: 0 })
    }
    ///Creates a new type constructor with the specified argument and kind
    pub fn new_op(name : InternedStr, types : ~[Type]) -> Type {
        Type::new_type_kind(TypeConstructor(TypeConstructor { name : name, kind: StarKind }), types)
    }
    ///Creates a new type constructor applied to the types and with a specific kind
    pub fn new_op_kind(name : InternedStr, types : ~[Type], kind: Kind) -> Type {
        let mut result = TypeConstructor(TypeConstructor { name : name, kind: kind });
        for typ in types.move_iter() {
            result = TypeApplication(box result, box typ);
        }
        result
    }
    fn new_type_kind(mut result: Type, types: ~[Type]) -> Type {
        *result.mut_kind() = Kind::new(types.len() as int + 1);
        for typ in types.move_iter() {
            result = TypeApplication(box result, box typ);
        }
        result
    }

    ///Returns a reference to the type variable or fails if it is not a variable
    pub fn var<'a>(&'a self) -> &'a TypeVariable {
        match self {
            &TypeVariable(ref var) => var,
            _ => fail!("Tried to unwrap {} as a TypeVariable", self)
        }
    }

    ///Returns a reference to the type constructor or fails if it is not a constructor
    #[allow(dead_code)]
    pub fn ctor<'a>(&'a self) -> &'a TypeConstructor {
        match self {
            &TypeConstructor(ref op) => op,
            _ => fail!("Tried to unwrap {} as a TypeConstructor", self)
        }
    }

    ///Returns a reference to the the type function or fails if it is not an application
    #[allow(dead_code)]
    pub fn appl<'a>(&'a self) -> &'a Type {
        match self {
            &TypeApplication(ref lhs, _) => { let l: &Type = *lhs; l }
            _ => fail!("Error: Tried to unwrap {} as TypeApplication", self)
        }
    }
    #[allow(dead_code)]
    ///Returns a reference to the the type argument or fails if it is not an application
    pub fn appr<'a>(&'a self) -> &'a Type {
        match self {
            &TypeApplication(_, ref rhs) => { let r: &Type = *rhs; r }
            _ => fail!("Error: Tried to unwrap TypeApplication")
        }
    }

    ///Returns the kind of the type
    ///Fails only if the type is a type application with an invalid kind
    pub fn kind<'a>(&'a self) -> &'a Kind {
        match self {
            &TypeVariable(ref v) => &v.kind,
            &TypeConstructor(ref v) => &v.kind,
            &TypeApplication(ref lhs, _) => 
                match lhs.kind() {
                    &KindFunction(_, ref k) => {
                        let kind: &Kind = *k;
                        kind
                    }
                    _ => fail!("Type application must have a kind of KindFunction, {}", self)
                },
            &Generic(ref v) => &v.kind
        }
    }
    ///Returns a mutable reference to the types kind
    pub fn mut_kind<'a>(&'a mut self) -> &'a mut Kind {
        match *self {
            TypeVariable(ref mut v) => &mut v.kind,
            TypeConstructor(ref mut v) => &mut v.kind,
            TypeApplication(ref mut lhs, _) => 
                match *lhs.mut_kind() {
                    KindFunction(_, ref mut k) => {
                        let kind: &mut Kind = *k;
                        kind
                    }
                    _ => fail!("Type application must have a kind of KindFunction")
                },
            Generic(ref mut v) => &mut v.kind
        }
    }
}

impl <S: Writer> ::std::hash::Hash<S> for TypeVariable {
    #[inline]
    fn hash(&self, state: &mut S) {
        //Only has the id since the kind should always be the same for two variables
        self.id.hash(state);
    }
}

///Constructs a string which holds the name of an n-tuple
pub fn tuple_name(n: uint) -> String {
    let mut ident = String::from_char(1, '(');
    for _ in range(1, n) {
        ident.push_char(',');
    }
    ident.push_char(')');
    ident
}
///Returns the type of an n-tuple constructor as well as the name of the tuple
pub fn tuple_type(n: uint) -> (String, Type) {
    let mut var_list = Vec::new();
    assert!(n < 26);
    for i in range(0, n) {
        let c = (('a' as u8) + i as u8) as char;
        var_list.push(Generic(Type::new_var_kind(intern(c.to_str().as_slice()), star_kind.clone()).var().clone()));
    }
    let ident = tuple_name(n);
    let mut typ = Type::new_op(intern(ident.as_slice()), FromVec::from_vec(var_list));
    for i in range_step(n as int - 1, -1, -1) {
        let c = (('a' as u8) + i as u8) as char;
        typ = function_type_(Generic(Type::new_var(intern(c.to_str().as_slice())).var().clone()), typ);
    }
    (ident, typ)
}
///Constructs a list type which holds elements of type 'typ'
pub fn list_type(typ: Type) -> Type {
    Type::new_op(intern("[]"), ~[typ])
}
///Returns the Type of the Char type
pub fn char_type() -> Type {
    Type::new_op(intern("Char"), ~[])
}
///Returns the type for the Int type
pub fn int_type() -> Type {
    Type::new_op(intern("Int"), ~[])
}
///Returns the type for the Bool type
pub fn bool_type() -> Type {
    Type::new_op(intern("Bool"), ~[])
}
///Returns the type for the Double type
pub fn double_type() -> Type {
    Type::new_op(intern("Double"), ~[])
}
///Creates a function type
pub fn function_type(arg: &Type, result: &Type) -> Type {
    function_type_(arg.clone(), result.clone())
}

///Creates a function type
pub fn function_type_(func : Type, arg : Type) -> Type {
    Type::new_op(intern("->"), ~[func, arg])
}

///Creates a IO type
pub fn io(typ: Type) -> Type {
    Type::new_op(intern("IO"), ~[typ])
}
///Returns the unit type '()'
pub fn unit() -> Type {
    Type::new_op(intern("()"), ~[])
}


#[deriving(Clone, PartialEq, Eq, Hash)]
pub struct Constraint {
    pub class : InternedStr,
    pub variables : ~[TypeVariable]
}

#[deriving(Clone, PartialEq, Eq, Hash)]
pub enum Kind {
    KindFunction(Box<Kind>, Box<Kind>),
    StarKind
}
impl fmt::Show for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &StarKind => write!(f, "*"),
            &KindFunction(ref lhs, ref rhs) => write!(f, "({} -> {})", *lhs, *rhs)
        }
    }
}

impl Kind {
    pub fn new(v: int) -> Kind {
        let mut kind = star_kind.clone();
        for _ in range(1, v) {
            kind = KindFunction(box StarKind, box kind);
        }
        kind
    }
}

impl Default for Kind {
    fn default() -> Kind {
        StarKind
    }
}
pub static unknown_kind : Kind = StarKind;
pub static star_kind : Kind = StarKind;

impl Default for Type {
    fn default() -> Type {
        Type::new_var(intern("a"))
    }
}
impl fmt::Show for TypeVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.id)
    }
}
impl fmt::Show for TypeConstructor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl <T: fmt::Show> fmt::Show for Qualified<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} => {}", self.constraints, self.value)
    }
}

#[deriving(PartialEq, PartialOrd)]
enum Prec_ {
    Top,
    Function,
    Constructor,
}
struct Prec<'a>(Prec_, &'a Type);

///If the type is a function it returns the type of the argument and the result type,
///otherwise it returns None
pub fn try_get_function<'a>(typ: &'a Type) -> Option<(&'a Type, &'a Type)> {
    match *typ {
        TypeApplication(ref xx, ref result) => {
            let y: &Type = *xx;
            match *y {
                TypeApplication(ref xx, ref arg) => {
                    let x: &Type = *xx;
                    match x {
                        &TypeConstructor(ref op) if "->" == op.name.as_slice() => {
                            let a: &Type = *arg;
                            let r: &Type = *result;
                            Some((a, r))
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

impl <'a> fmt::Show for Prec<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Prec(p, t) = *self;
        match *t {
            TypeVariable(ref var) => write!(f, "{}", *var),
            TypeConstructor(ref op) => write!(f, "{}", *op),
            Generic(ref var) => write!(f, "\\#{}", *var),
            TypeApplication(ref lhs, ref rhs) => {
                match try_get_function(t) {
                    Some((arg, result)) => {
                        if p >= Function {
                            write!(f, "({} -> {})", *arg, result)
                        }
                        else {
                            write!(f, "{} -> {}", Prec(Function, arg), result)
                        }
                    }
                    None => {
                        match **lhs {
                            TypeConstructor(ref op) if "[]" == op.name.as_slice() => {
                                write!(f, "[{}]", rhs)
                            }
                            _ => {
                                if p >= Constructor {
                                    write!(f, "({} {})", Prec(Function, *lhs), Prec(Constructor, *rhs))
                                }
                                else {
                                    write!(f, "{} {}", Prec(Function, *lhs), Prec(Constructor, *rhs))
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

impl fmt::Show for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", Prec(Top, self))
    }
}
impl fmt::Show for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{}", self.class));
        for var in self.variables.iter() {
            try!(write!(f, " {}", *var));
        }
        Ok(())
    }
}
fn type_eq<'a>(mapping: &mut HashMap<&'a TypeVariable, &'a TypeVariable>, lhs: &'a Type, rhs: &'a Type) -> bool {
    match (lhs, rhs) {
        (&TypeConstructor(ref l), &TypeConstructor(ref r)) => l.name == r.name,
        (&TypeVariable(ref r), &TypeVariable(ref l)) => var_eq(mapping, r, l),
        (&TypeApplication(ref lhs1, ref rhs1), &TypeApplication(ref lhs2, ref rhs2)) => {
            type_eq(mapping, *lhs1, *lhs2) && type_eq(mapping, *rhs1, *rhs2)
        }
        _ => false
    }
}

fn var_eq<'a>(mapping: &mut HashMap<&'a TypeVariable, &'a TypeVariable>, l: &'a TypeVariable, r: &'a TypeVariable) -> bool {
    match mapping.find(&l) {
        Some(x) => return x.id == r.id,
        None => ()
    }
    mapping.insert(l, r);
    true
}

impl PartialEq for Qualified<Type> {
    fn eq(&self, other: &Qualified<Type>) -> bool {
        let mut mapping = HashMap::new();
        self.constraints.iter()
            .zip(other.constraints.iter())
            .all(|(l, r)| l.class == r.class && var_eq(&mut mapping, &l.variables[0], &r.variables[0]))
        && type_eq(&mut mapping, &self.value, &other.value)
    }
}
impl Eq for Qualified<Type> {
}

impl PartialEq for Type {
    ///Compares two types, treating two type variables as equal as long as they always and only appear at the same place
    ///a -> b == c -> d
    ///a -> b != c -> c
    fn eq(&self, other: &Type) -> bool {
        let mut mapping = HashMap::new();
        type_eq(&mut mapping, self, other)
    }
}


