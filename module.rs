use std::rc::Rc;
use std::cell::RefCell;
use std::fmt;
use std::hashmap::HashMap;
use lexer::Location;
pub struct Module {
    name : ~str,
    bindings : ~[Binding],
    typeDeclarations : ~[TypeDeclaration],
    classes : ~[Class],
    instances : ~[Instance],
    dataDefinitions : ~[DataDefinition]
}

pub struct Class {
    name : ~str,
    variable: TypeVariable,
    declarations : ~[TypeDeclaration]
}

pub struct Instance {
    bindings : ~[Binding],
    typ : TypeOperator,
    classname : ~str
}

#[deriving(Eq)]
pub struct Binding {
    name : ~str,
    expression : TypedExpr,
    typeDecl : TypeDeclaration,
    arity : int
}

#[deriving(Eq)]
pub struct Constructor {
    name : ~str,
    typ : Type,
    tag : int,
    arity : int
}

#[deriving(Eq)]
pub struct DataDefinition {
    constructors : ~[Constructor],
    typ : TypeOperator,
    parameters : HashMap<~str, Type>
}

#[deriving(Clone, Eq, Default)]
pub struct TypeDeclaration {
    context : ~[TypeOperator],
    typ : Type,
    name : ~str
}

#[deriving(Clone, Default, ToStr)]
pub struct TypeOperator {
    name : ~str,
    types : ~[Type]
}
#[deriving(Clone, Eq, Default, ToStr, IterBytes)]
pub struct TypeVariable {
    id : int
}
#[deriving(Clone, ToStr)]
pub enum Type {
    TypeVariable(TypeVariable),
    TypeOperator(TypeOperator)
}

impl Default for Type {
    fn default() -> Type {
        Type::new_var(-1)
    }
}

fn operator_eq(mapping: &mut HashMap<TypeVariable, TypeVariable>, lhs: &TypeOperator, rhs: &TypeOperator) -> bool {
    lhs.name == rhs.name && lhs.types.len() == rhs.types.len()
    && lhs.types.iter().zip(rhs.types.iter()).all(|(l, r)| type_eq(mapping, l, r))
}

impl Eq for TypeOperator {
    fn eq(&self, other: &TypeOperator) -> bool {
        let mut mapping = HashMap::new();
        operator_eq(&mut mapping, self, other)
    }
}

fn type_eq(mapping: &mut HashMap<TypeVariable, TypeVariable>, lhs: &Type, rhs: &Type) -> bool {
    match (lhs, rhs) {
        (&TypeOperator(ref l), &TypeOperator(ref r)) => operator_eq(mapping, l, r),
        (&TypeVariable(ref r), &TypeVariable(ref l)) => {
            match mapping.find(l) {
                Some(x) => return x.id == r.id,
                None => ()
            }
            mapping.insert(*l, *r);
            true
        }
        _ => false
    }
}

impl Eq for Type {
    fn eq(&self, other: &Type) -> bool {
        let mut mapping = HashMap::new();
        type_eq(&mut mapping, self, other)
    }
}

impl Type {
    pub fn new_var(id : int) -> Type {
        TypeVariable(TypeVariable { id : id })
    }
    pub fn new_op(name : ~str, types : ~[Type]) -> Type {
        TypeOperator(TypeOperator { name : name, types : types })
    }
}

pub struct TypedExpr {
    expr : Expr,
    typ : Rc<RefCell<Type>>,
    location : Location
}

impl Eq for TypedExpr {
    fn eq(&self, other : &TypedExpr) -> bool {
        self.expr == other.expr
    }
}

impl fmt::Default for ~TypedExpr {
    fn fmt(expr: &~TypedExpr, f: &mut fmt::Formatter) {
        write!(f.buf, "{}", expr.expr)
    }
}

impl TypedExpr {
    pub fn new(expr : Expr) -> TypedExpr {
        TypedExpr { expr : expr, typ : Rc::from_mut(RefCell::new(TypeVariable(TypeVariable { id : 0 }))), location : Location { column : -1, row : -1, absolute : -1 } }
    }
    pub fn with_location(expr : Expr, loc : Location) -> TypedExpr {
        TypedExpr { expr : expr, typ : Rc::from_mut(RefCell::new(TypeVariable(TypeVariable { id : 0 }))), location : loc }
    }
}

#[deriving(Eq)]
pub struct Alternative {
    pattern : Pattern,
    expression : TypedExpr
}

#[deriving(Eq)]
pub enum Pattern {
    NumberPattern(int),
    IdentifierPattern(~str),
    ConstructorPattern(~str, ~[Pattern])
}

#[deriving(Eq)]
pub enum Expr {
    Identifier(~str),
    Apply(~TypedExpr, ~TypedExpr),
    Number(int),
    Lambda(~str, ~TypedExpr),
    Let(~[Binding], ~TypedExpr),
    Case(~TypedExpr, ~[Alternative])
}

impl fmt::Default for Expr {
    fn fmt(expr: &Expr, f: &mut fmt::Formatter) {
        match expr {
            &Identifier(ref s) => write!(f.buf, "{}", *s),
            &Apply(ref func, ref arg) => write!(f.buf, "({} {})", *func, *arg),
            &Number(num) => write!(f.buf, "{}", num),
            &Lambda(ref arg, ref body) => write!(f.buf, "({} -> {})", *arg, *body),
            &Let(_,_) => write!(f.buf, "Let ... "),
            &Case(_,_) => write!(f.buf, "Case ...")
        }
    }
}
impl fmt::Default for ~Expr {
    fn fmt(expr: &~Expr, f: &mut fmt::Formatter) {
        write!(f.buf, "{}", *expr)
    }
}
