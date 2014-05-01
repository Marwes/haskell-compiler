use std::fmt;
use collections::HashMap;
use std::iter::range_step;
pub use std::default::Default;
pub use lexer::{Location, Located};

pub struct Module<Ident = ~str> {
    pub name : Ident,
    pub bindings : ~[Binding<Ident>],
    pub typeDeclarations : ~[TypeDeclaration],
    pub classes : ~[Class],
    pub instances : ~[Instance<Ident>],
    pub dataDefinitions : ~[DataDefinition<Ident>]
}
#[deriving(Clone)]
pub struct Class<Ident = ~str> {
    pub name : Ident,
    pub variable : TypeVariable,
    pub declarations : ~[TypeDeclaration]
}

pub struct Instance<Ident = ~str> {
    pub bindings : ~[Binding<Ident>],
    pub constraints : ~[Constraint],
    pub typ : Type,
    pub classname : ~str
}

#[deriving(Eq)]
pub struct Binding<Ident = ~str> {
    pub name : Ident,
    pub expression : TypedExpr<Ident>,
    pub typeDecl : TypeDeclaration,
    pub arity : uint
}

#[deriving(Eq, TotalEq, Clone, Show)]
pub struct Constructor<Ident = ~str> {
    pub name : Ident,
    pub typ : Type,
    pub tag : int,
    pub arity : int
}

#[deriving(Eq, Clone)]
pub struct DataDefinition<Ident = ~str> {
    pub constructors : ~[Constructor<Ident>],
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
    TypeApplication(~Type, ~Type),
    Generic(TypeVariable)
}

impl Type {

    pub fn new_var(id : int) -> Type {
        TypeVariable(TypeVariable { id : id, kind: unknown_kind.clone() })
    }
    pub fn new_var_args(id: int, types : ~[Type]) -> Type {
        let mut result = TypeVariable(TypeVariable { id : id, kind: Kind::new(types.len() as int + 1) });
        for typ in types.move_iter() {
            result = TypeApplication(~result, ~typ);
        }
        result
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
                },
            &Generic(_) => fail!("Generic has no kind")
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

pub fn tuple_type(size: uint) -> (~str, Type) {
    let mut var_list = Vec::new();
    for i in range(0, size) {
        var_list.push(Generic(Type::new_var_kind(i as int, star_kind.clone()).var().clone()));
    }
    let mut ident = StrBuf::from_char(1, '(');
    for _ in range(1, size) {
        ident.push_char(',');
    }
    ident.push_char(')');
    let result = ident.into_owned();
    let mut typ = Type::new_op(result.clone(), var_list.move_iter().collect());
    for i in range_step(size as int - 1, -1, -1) {
        typ = Type::new_op(~"->", ~[Generic(Type::new_var(i).var().clone()), typ]);
    }
    (result, typ)
}

pub fn list_type(typ: Type) -> Type {
    Type::new_op(~"[]", ~[typ])
}

pub fn char_type() -> Type {
    Type::new_op(~"Char", ~[])
}

pub fn function_type(func : &Type, arg : &Type) -> Type {
    Type::new_op(~"->", ~[func.clone(), arg.clone()])
}

pub fn function_type_(func : Type, arg : Type) -> Type {
    Type::new_op(~"->", ~[func, arg])
}

pub fn io(typ: Type) -> Type {
    Type::new_op("IO".to_owned(), ~[typ])
}
pub fn unit() -> Type {
    Type::new_op("()".to_owned(), ~[])
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
            &Generic(ref var) => write!(f.buf, "\\#{}", *var),
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
                    let x = match l {
                        &TypeApplication(_, ref x) => x,
                        _ => fail!()
                    };
                    if is_lhs_func {
                        write!(f.buf, "({}) -> {}", lhs, rhs)
                    }
                    else {
                        write!(f.buf, "{} -> {}", *x, rhs)
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

pub struct TypedExpr<Ident = ~str> {
    pub expr : Expr<Ident>,
    pub typ : Type,
    pub location : Location
}

impl <T: Eq> Eq for TypedExpr<T> {
    fn eq(&self, other : &TypedExpr<T>) -> bool {
        self.expr == other.expr
    }
}

impl fmt::Show for TypedExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f.buf, "{}", self.expr)
    }
}

impl TypedExpr {
    pub fn new<T>(expr : Expr<T>) -> TypedExpr<T> {
        TypedExpr { expr : expr, typ : Type::new_var(0), location : Location { column : -1, row : -1, absolute : -1 } }
    }
    pub fn with_location<T>(expr : Expr<T>, loc : Location) -> TypedExpr<T> {
        TypedExpr { expr : expr, typ : Type::new_var(0), location : loc }
    }
}

#[deriving(Eq)]
pub struct Alternative<Ident = ~str> {
    pub pattern : Located<Pattern<Ident>>,
    pub expression : TypedExpr<Ident>
}

#[deriving(Eq, TotalEq)]
pub enum Pattern<Ident = ~str> {
    NumberPattern(int),
    IdentifierPattern(Ident),
    ConstructorPattern(Ident, ~[Pattern<Ident>])
}

#[deriving(Eq)]
pub enum DoBinding<Ident = ~str> {
    DoLet(~[Binding<Ident>]),
    DoBind(Located<Pattern<Ident>>, TypedExpr<Ident>),
    DoExpr(TypedExpr<Ident>)
}

#[deriving(Eq)]
pub enum Expr<Ident = ~str> {
    Identifier(Ident),
    Apply(~TypedExpr<Ident>, ~TypedExpr<Ident>),
    Number(int),
    Rational(f64),
    String(~str),
    Char(char),
    Lambda(Ident, ~TypedExpr<Ident>),
    Let(~[Binding<Ident>], ~TypedExpr<Ident>),
    Case(~TypedExpr<Ident>, ~[Alternative<Ident>]),
    Do(~[DoBinding<Ident>], ~TypedExpr<Ident>)
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
            &Let(ref bindings, ref body) => {
                try!(write!(f.buf, "let \\{\n"));
                for bind in bindings.iter() {
                    try!(write!(f.buf, "; {} = {}\n", bind.name, bind.expression));
                }
                write!(f.buf, "\\} in {}\n", *body)
            }
            &Case(ref expr, ref alts) => {
                try!(write!(f.buf, "case {} of \\{\n", *expr));
                for alt in alts.iter() {
                    try!(write!(f.buf, "; {} -> {}\n", alt.pattern.node, alt.expression));
                }
                write!(f.buf, "\\}\n")
            }
            _ => fail!("Show not implemented for expr")
        }
    }
}
impl <T: fmt::Show> fmt::Show for Pattern<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &IdentifierPattern(ref s) => write!(f.buf, "{}", s),
            &NumberPattern(ref i) => write!(f.buf, "{}", i),
            &ConstructorPattern(ref name, ref patterns) => {
                try!(write!(f.buf, "({}", name));
                for p in patterns.iter() {
                    try!(write!(f.buf, "{} ", p));
                }
                write!(f.buf, ")")
            }
        }
    }
}

pub trait Visitor<Ident> {
    fn visit_expr(&mut self, expr: &TypedExpr<Ident>) {
        walk_expr(self, expr)
    }
    fn visit_alternative(&mut self, alt: &Alternative<Ident>) {
        walk_alternative(self, alt)
    }
    fn visit_pattern(&mut self, pattern: &Pattern<Ident>) {
        walk_pattern(self, pattern)
    }
    fn visit_binding(&mut self, binding: &Binding<Ident>) {
        walk_binding(self, binding);
    }
    fn visit_module(&mut self, module: &Module<Ident>) {
        walk_module(self, module);
    }
}

pub fn walk_module<Ident>(visitor: &mut Visitor<Ident>, module: &Module<Ident>) {
    for bind in module.instances.iter().flat_map(|i| i.bindings.iter()) {
        visitor.visit_binding(bind);
    }
    for bind in module.bindings.iter() {
        visitor.visit_binding(bind);
    }
}

pub fn walk_binding<Ident>(visitor: &mut Visitor<Ident>, binding: &Binding<Ident>) {
    visitor.visit_expr(&binding.expression);
}

pub fn walk_expr<Ident>(visitor: &mut Visitor<Ident>, expr: &TypedExpr<Ident>) {
    match &expr.expr {
        &Apply(ref func, ref arg) => {
            visitor.visit_expr(*func);
            visitor.visit_expr(*arg);
        }
        &Lambda(_, ref body) => visitor.visit_expr(*body),
        &Let(ref binds, ref e) => {
            for b in binds.iter() {
                visitor.visit_binding(b);
            }
            visitor.visit_expr(*e);
        }
        &Case(ref e, ref alts) => {
            visitor.visit_expr(*e);
            for alt in alts.iter() {
                visitor.visit_alternative(alt);
            }
        }
        _ => ()
    }
}

pub fn walk_alternative<Ident>(visitor: &mut Visitor<Ident>, alt: &Alternative<Ident>) {
    visitor.visit_expr(&alt.expression);
}

pub fn walk_pattern<Ident>(visitor: &mut Visitor<Ident>, pattern: &Pattern<Ident>) {
    match pattern {
        &ConstructorPattern(_, ref ps) => {
            for p in ps.iter() {
                visitor.visit_pattern(p);
            }
        }
        _ => ()
    }
}
