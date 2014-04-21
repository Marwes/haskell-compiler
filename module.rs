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
    pub name : ~str,
    pub kind : Kind
}
#[deriving(Clone, Eq, TotalEq, Default, Hash)]
pub struct TypeVariable {
    pub id : int,
    pub kind : Kind
}
#[deriving(Clone, TotalEq, Hash)]
pub enum Type {
    TypeVariable(TypeVariable),
    TypeOperator(TypeOperator),
    TypeApplication(~Type, ~Type)
}

impl Type {

    pub fn new_var(id : int) -> Type {
        TypeVariable(TypeVariable { id : id, kind: unknown_kind.clone() })
    }
    pub fn new_var_kind(id : int, kind: Kind) -> Type {
        TypeVariable(TypeVariable { id : id, kind: kind })
    }
    pub fn new_op(name : ~str, types : ~[Type]) -> Type {
        let mut result = TypeOperator(TypeOperator { name : name, kind: Kind::new(types.len() as int + 1) });
        for typ in types.move_iter() {
            result = TypeApplication(~result, ~typ);
        }
        result
    }
    pub fn new_op_kind(name : ~str, types : ~[Type], kind: Kind) -> Type {
        let mut result = TypeOperator(TypeOperator { name : name, kind: kind });
        for typ in types.move_iter() {
            result = TypeApplication(~result, ~typ);
        }
        result
    }

    pub fn var<'a>(&'a self) -> &'a TypeVariable {
        match self {
            &TypeVariable(ref var) => var,
            _ => fail!("Tried to unwrap {} as a TypeVariable", self)
        }
    }
    #[allow(dead_code)]
    pub fn op<'a>(&'a self) -> &'a TypeOperator {
        match self {
            &TypeOperator(ref op) => op,
            _ => fail!("Tried to unwrap {} as a TypeOperator", self)
        }
    }
    #[allow(dead_code)]
    pub fn appl<'a>(&'a self) -> &'a Type {
        match self {
            &TypeApplication(ref lhs, _) => { let l: &Type = *lhs; l }
            _ => fail!("Error: Tried to unwrap {} as TypeApplication", self)
        }
    }
    #[allow(dead_code)]
    pub fn appr<'a>(&'a self) -> &'a Type {
        match self {
            &TypeApplication(_, ref rhs) => { let r: &Type = *rhs; r }
            _ => fail!("Error: Tried to unwrap TypeApplication")
        }
    }

    pub fn kind<'a>(&'a self) -> &'a Kind {
        match self {
            &TypeVariable(ref v) => &v.kind,
            &TypeOperator(ref v) => &v.kind,
            &TypeApplication(ref lhs, _) => 
                match lhs.kind() {
                    &KindFunction(_, ref k) => {
                        let kind: &Kind = *k;
                        kind
                    }
                    _ => fail!("Type application must have a kind of KindFunction, {}", self)
                }
        }
    }
    pub fn mut_kind<'a>(&'a mut self) -> &'a mut Kind {
        match self {
            &TypeVariable(ref mut v) => &mut v.kind,
            &TypeOperator(ref mut v) => &mut v.kind,
            _ => fail!("Typeapplication has no kind")
        }
    }
}

#[deriving(Clone, Eq, TotalEq, Hash)]
pub struct Constraint {
    pub class : ~str,
    pub variables : ~[TypeVariable]
}

#[deriving(Clone, Eq, TotalEq, Hash)]
pub enum Kind {
    KindFunction(~Kind, ~Kind),
    StarKind
}
impl fmt::Show for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &StarKind => write!(f.buf, "*"),
            &KindFunction(ref lhs, ref rhs) => write!(f.buf, "({} -> {})", *lhs, *rhs)
        }
    }
}

impl Kind {
    pub fn new(v: int) -> Kind {
        let mut kind = star_kind.clone();
        for _ in range(1, v) {
            kind = KindFunction(~StarKind, ~kind);
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

impl fmt::Show for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &TypeVariable(ref var) => write!(f.buf, "{}", *var),
            &TypeOperator(ref op) => write!(f.buf, "{}", *op),
            &TypeApplication(ref lhs, ref rhs) => {
                let l: &Type = *lhs;
                let is_list = match l {
                    &TypeOperator(ref op) => "[]" == op.name,
                    _ => false
                };
                let is_func = match l {
                    &TypeApplication(ref xx, _) => {
                        let x: &Type = *xx;
                        match x {
                            &TypeOperator(ref op) => "->" == op.name,
                            _ => false
                        }
                    }
                    _ => false
                };
                if is_func {
                    let is_lhs_func = match l {
                        &TypeApplication(ref x, _) => {
                            let xx: &Type = *x;
                            match xx {
                                &TypeApplication(ref y, _) => {
                                    let yy: &Type = *y;
                                    match yy {
                                        &TypeOperator(ref op) => "->" == op.name,
                                        _ => false
                                    }
                                }
                                _ => false
                            }
                        }
                        _ => false
                    };
                    if is_lhs_func {
                        write!(f.buf, "({}) -> {}", lhs, rhs)
                    }
                    else {
                        write!(f.buf, "{} -> {}", lhs, rhs)
                    }
                }
                else {
                    if is_list {
                        try!(write!(f.buf, "["));
                    }
                    else {
                        try!(write!(f.buf, "({} ", lhs));
                    }
                    try!(write!(f.buf, "{}", rhs));
                    if is_list {
                        write!(f.buf, "]")
                    }
                    else {
                        write!(f.buf, ")")
                    }
                }
            }
        }
    }
}
impl fmt::Show for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f.buf, "{}", self.class));
        for var in self.variables.iter() {
            try!(write!(f.buf, " {}", *var));
        }
        Ok(())
    }
}
impl fmt::Show for TypeDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f.buf, "{} :: ", self.name));
        for constraint in self.context.iter() {
            try!(write!(f.buf, "{} ", *constraint));
        }
        if self.context.len() > 0 {
            try!(write!(f.buf, "=> "));
        }
        write!(f.buf, "{}", self.typ)
    }
}

fn type_eq<'a>(mapping: &mut HashMap<&'a TypeVariable, &'a TypeVariable>, lhs: &'a Type, rhs: &'a Type) -> bool {
    match (lhs, rhs) {
        (&TypeOperator(ref l), &TypeOperator(ref r)) => l.name == r.name,
        (&TypeVariable(ref r), &TypeVariable(ref l)) => {
            match mapping.find(&l) {
                Some(x) => return x.id == r.id,
                None => ()
            }
            mapping.insert(l, r);
            true
        }
        (&TypeApplication(ref lhs1, ref rhs1), &TypeApplication(ref lhs2, ref rhs2)) => {
            type_eq(mapping, *lhs1, *lhs2) && type_eq(mapping, *rhs1, *rhs2)
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
