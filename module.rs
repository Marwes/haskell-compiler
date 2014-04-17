use std::fmt;
use collections::HashMap;
pub use std::default::Default;
pub use lexer::{Location, Located};

pub struct Module {
    pub name : ~str,
    pub bindings : ~[Binding],
    pub typeDeclarations : ~[TypeDeclaration],
    pub classes : ~[Class],
    pub instances : ~[Instance],
    pub dataDefinitions : ~[DataDefinition]
}
#[deriving(Clone)]
pub struct Class {
    pub name : ~str,
    pub variable : TypeVariable,
    pub declarations : ~[TypeDeclaration]
}

pub struct Instance {
    pub bindings : ~[Binding],
    pub constraints : ~[Constraint],
    pub typ : Type,
    pub classname : ~str
}

#[deriving(Eq)]
pub struct Binding {
    pub name : ~str,
    pub expression : TypedExpr,
    pub typeDecl : TypeDeclaration,
    pub arity : uint
}

#[deriving(Eq, TotalEq, Clone, Show)]
pub struct Constructor {
    pub name : ~str,
    pub typ : Type,
    pub tag : int,
    pub arity : int
}

#[deriving(Eq, Clone)]
pub struct DataDefinition {
    pub constructors : ~[Constructor],
    pub typ : Type,
    pub parameters : HashMap<~str, int>
}

#[deriving(Clone, Eq, TotalEq, Default)]
pub struct TypeDeclaration {
    pub context : ~[Constraint],
    pub typ : Type,
    pub name : ~str
}

#[deriving(Clone, Default, Eq, TotalEq, Hash)]
pub struct TypeOperator {
    pub name : ~str
}
#[deriving(Clone, Eq, TotalEq, Default, Hash)]
pub struct TypeVariable {
    pub id : int
}
#[deriving(Clone, Eq, TotalEq, Hash)]
pub enum Type_ {
    TypeVariable(TypeVariable),
    TypeOperator(TypeOperator)
}

#[deriving(Clone, Eq, TotalEq, Hash)]
pub struct Constraint {
    pub class : ~str,
    pub variables : ~[TypeVariable]
}

#[deriving(Clone, TotalEq, Hash)]
pub struct Type {
    pub typ : Type_,
    pub types : ~[Type]
}

impl Default for Type {
    fn default() -> Type {
        Type::new_var(-1)
    }
}
impl fmt::Show for TypeVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f.buf, "{}", self.id)
    }
}
impl fmt::Show for TypeOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f.buf, "{}", self.name)
    }
}
impl fmt::Show for Type_ {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &TypeVariable(ref var) => write!(f.buf, "{}", *var),
            &TypeOperator(ref op) => write!(f.buf, "{}", *op)
        }
    }
}
impl fmt::Show for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let typ = self;
        if typ.types.len() == 0 {
            write!(f.buf, "{}", typ.typ)
        }
        else {
            let is_list = match &typ.typ {
                &TypeOperator(ref op) => "[]" == op.name,
                _ => false
            };
            let is_func = match &typ.typ {
                &TypeOperator(ref op) => "->" == op.name,
                _ => false
            };
            if is_list {
                write!(f.buf, "[");
            }
            else if is_func {
                let is_lhs_func = match &typ.types[0].typ {
                    &TypeOperator(ref op) => "->" == op.name,
                    _ => false
                };
                if is_lhs_func {
                    return write!(f.buf, "({}) -> {}", typ.types[0], typ.types[1]);
                }
                else {
                    return write!(f.buf, "{} -> {}", typ.types[0], typ.types[1]);
                }
            }
            else {
                write!(f.buf, "({}", typ.typ);
            }
            for t in typ.types.iter() {
                write!(f.buf, " {}", *t);
            }
            if is_list {
                write!(f.buf, "]")
            }
            else {
                write!(f.buf, ")")
            }
        }
    }
}
impl fmt::Show for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f.buf, "{}", self.class);
        for var in self.variables.iter() {
            write!(f.buf, " {}", *var);
        }
        Ok(())
    }
}
impl fmt::Show for TypeDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for constraint in self.context.iter() {
            write!(f.buf, "{} ", *constraint);
        }
        if self.context.len() > 0 {
            write!(f.buf, "=> ");
        }
        write!(f.buf, "{}", self.typ)
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
    pub expr : Expr,
    pub typ : Type,
    pub location : Location
}

impl Eq for TypedExpr {
    fn eq(&self, other : &TypedExpr) -> bool {
        self.expr == other.expr
    }
}

impl fmt::Show for TypedExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f.buf, "{}", self.expr)
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
    pub pattern : Located<Pattern>,
    pub expression : TypedExpr
}

#[deriving(Eq, TotalEq)]
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

impl fmt::Show for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
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
