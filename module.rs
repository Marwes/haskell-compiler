use std::fmt;
use std::hashmap::HashMap;
pub use lexer::{Location, Located};

pub struct Module {
    name : ~str,
    bindings : ~[Binding],
    typeDeclarations : ~[TypeDeclaration],
    classes : ~[Class],
    instances : ~[Instance],
    dataDefinitions : ~[DataDefinition]
}
#[deriving(Clone)]
pub struct Class {
    name : ~str,
    variable: TypeVariable,
    declarations : ~[TypeDeclaration]
}

pub struct Instance {
    bindings : ~[Binding],
    constraints: ~[Constraint],
    typ : Type,
    classname : ~str
}

#[deriving(Eq)]
pub struct Binding {
    name : ~str,
    expression : TypedExpr,
    typeDecl : TypeDeclaration,
    arity : uint
}

#[deriving(Eq, Clone)]
pub struct Constructor {
    name : ~str,
    typ : Type,
    tag : int,
    arity : int
}

#[deriving(Eq, Clone)]
pub struct DataDefinition {
    constructors: ~[Constructor],
    typ: Type,
    parameters: HashMap<~str, int>
}

#[deriving(Clone, Eq, Default)]
pub struct TypeDeclaration {
    context : ~[Constraint],
    typ : Type,
    name : ~str
}

#[deriving(Clone, Default, Eq, ToStr, IterBytes)]
pub struct TypeOperator {
    name : ~str
}
#[deriving(Clone, Eq, Default, ToStr, IterBytes)]
pub struct TypeVariable {
    id : int
}
#[deriving(Clone, ToStr, IterBytes)]
pub enum Type_ {
    TypeVariable(TypeVariable),
    TypeOperator(TypeOperator)
}

#[deriving(Clone, Eq, ToStr, IterBytes)]
pub struct Constraint {
    class: ~str,
    variables: ~[TypeVariable]
}

#[deriving(Clone, ToStr, IterBytes)]
pub struct Type {
    typ: Type_,
    types: ~[Type]
}

impl Default for Type {
    fn default() -> Type {
        Type::new_var(-1)
    }
}
impl fmt::Default for TypeVariable {
    fn fmt(var : &TypeVariable, f: &mut fmt::Formatter) {
        write!(f.buf, "{}", var.id)
    }
}
impl fmt::Default for TypeOperator {
    fn fmt(op: &TypeOperator, f: &mut fmt::Formatter) {
        write!(f.buf, "{}", op.name)
    }
}
impl fmt::Default for Type {
    fn fmt(typ : &Type, f: &mut fmt::Formatter) {
        if typ.types.len() == 0 {
            match &typ.typ {
                &TypeVariable(ref var) => write!(f.buf, "{}", *var),
                &TypeOperator(ref op) => write!(f.buf, "{}", *op)
            }
        }
        else {
            write!(f.buf, "(");
            match &typ.typ {
                &TypeVariable(ref var) => write!(f.buf, "{}", *var),
                &TypeOperator(ref op) => write!(f.buf, "{}", *op)
            }
            for t in typ.types.iter() {
                write!(f.buf, " {}", *t);
            }
            write!(f.buf, ")");
        }
    }
}

fn type_eq<'a>(mapping: &mut HashMap<&'a TypeVariable, &'a TypeVariable>, lhs: &'a Type, rhs: &'a Type) -> bool {
    let equal = match (&lhs.typ, &rhs.typ) {
        (&TypeOperator(ref l), &TypeOperator(ref r)) => l == r,
        (&TypeVariable(ref r), &TypeVariable(ref l)) => {
            match mapping.find(&l) {
                Some(x) => return x.id == r.id,
                None => ()
            }
            mapping.insert(l, r);
            true
        }
        _ => false
    };
    equal && lhs.types.len() == rhs.types.len()
    && lhs.types.iter().zip(rhs.types.iter()).all(|(l, r)| type_eq(mapping, l, r))
}

impl Eq for Type {
    fn eq(&self, other: &Type) -> bool {
        let mut mapping = HashMap::new();
        type_eq(&mut mapping, self, other)
    }
}

impl Type {
    pub fn new_var(id : int) -> Type {
        Type { typ: TypeVariable(TypeVariable { id : id }), types: ~[] }
    }
    pub fn new_op(name : ~str, types : ~[Type]) -> Type {
        Type { typ: TypeOperator(TypeOperator { name : name }), types : types }
    }

    pub fn var<'a>(&'a self) -> &'a TypeVariable {
        match &self.typ {
            &TypeVariable(ref var) => var,
            _ => fail!("Tried to unwrap TypeOperator as a TypeVariable")
        }
    }
    #[allow(dead_code)]
    pub fn op<'a>(&'a self) -> &'a TypeOperator {
        match &self.typ {
            &TypeOperator(ref op) => op,
            _ => fail!("Tried to unwrap TypeVariable as a TypeOperator")
        }
    }
}

pub struct TypedExpr {
    expr : Expr,
    typ : Type,
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
        TypedExpr { expr : expr, typ : Type::new_var(0), location : Location { column : -1, row : -1, absolute : -1 } }
    }
    pub fn with_location(expr : Expr, loc : Location) -> TypedExpr {
        TypedExpr { expr : expr, typ : Type::new_var(0), location : loc }
    }
}

#[deriving(Eq)]
pub struct Alternative {
    pattern : Located<Pattern>,
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
    Rational(f64),
    String(~str),
    Char(char),
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
            &Rational(num) => write!(f.buf, "{}", num),
            &String(ref s) => write!(f.buf, "\"{}\"", *s),
            &Char(c) => write!(f.buf, "'{}'", c),
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
