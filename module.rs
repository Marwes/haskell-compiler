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
    declarations : ~[TypeDeclaration]
}

pub struct Instance {
    bindings : ~[Binding],
    typ : TypeOperator,
    classname : ~str
}

pub struct Binding {
    name : ~str,
    expression : Typed<Expr>,
    typeDecl : TypeDeclaration,
    arity : int
}

pub struct Constructor {
    name : ~str,
    typ : Type,
    tag : int,
    arity : int
}

pub struct DataDefinition {
    constructors : ~[Constructor],
    typ : TypeOperator,
    parameters : HashMap<~str, Type>
}

#[deriving(Clone)]
pub struct TypeDeclaration {
    context : ~[TypeOperator],
    typ : Type,
    name : ~str
}

#[deriving(Clone, Eq, ToStr)]
pub struct TypeOperator {
    name : ~str,
    types : ~[Type]
}
#[deriving(Clone, Eq, ToStr, IterBytes)]
pub struct TypeVariable {
    id : int
}
#[deriving(Clone, Eq, ToStr)]
pub enum Type {
    TypeVariable(TypeVariable),
    TypeOperator(TypeOperator)
}

impl Type {
    pub fn new_var(id : int) -> Type {
        TypeVariable(TypeVariable { id : id })
    }
    pub fn new_op(name : ~str, types : ~[Type]) -> Type {
        TypeOperator(TypeOperator { name : name, types : types })
    }
}

pub struct Typed<T> {
    expr : T,
    typ : @mut Type,
    location : Location
}

impl <T : Eq> Eq for Typed<T> {
    fn eq(&self, other : &Typed<T>) -> bool {
        self.expr == other.expr
    }
}

impl <T : fmt::Default> fmt::Default for ~Typed<T> {
    fn fmt(expr: &~Typed<T>, f: &mut fmt::Formatter) {
        write!(f.buf, "{}", expr.expr)
    }
}

impl <T> Typed<T> {
    pub fn new(expr : T) -> Typed<T> {
        Typed { expr : expr, typ : @mut TypeVariable(TypeVariable { id : 0 }), location : Location { column : -1, row : -1, absolute : -1 } }
    }
    pub fn with_location(expr : T, loc : Location) -> Typed<T> {
        Typed { expr : expr, typ : @mut TypeVariable(TypeVariable { id : 0 }), location : loc }
    }
}

#[deriving(Eq)]
pub struct Alternative {
    pattern : Pattern,
    expression : Typed<Expr>
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
    Apply(~Typed<Expr>, ~Typed<Expr>),
    Number(int),
    Lambda(~str, ~Typed<Expr>),
    Let(~[(~str, ~Typed<Expr>)], ~Typed<Expr>),
    Case(~Typed<Expr>, ~[Alternative])
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
