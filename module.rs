use std::fmt;
use collections::HashMap;
use std::iter::range_step;
use interner::{intern, InternedStr};
use std::vec::FromVec;
pub use std::default::Default;
pub use lexer::{Location, Located};

#[deriving(Clone)]
pub struct Module<Ident = InternedStr> {
    pub name : Ident,
    pub imports: ~[Import],
    pub bindings : ~[Binding<Ident>],
    pub typeDeclarations : ~[TypeDeclaration],
    pub classes : ~[Class],
    pub instances : ~[Instance<Ident>],
    pub dataDefinitions : ~[DataDefinition<Ident>]
}

#[deriving(Clone)]
pub struct Import {
    pub module: InternedStr
}

#[deriving(Clone)]
pub struct Class<Ident = InternedStr> {
    pub name : Ident,
    pub variable : TypeVariable,
    pub declarations : ~[TypeDeclaration]
}

#[deriving(Clone)]
pub struct Instance<Ident = InternedStr> {
    pub bindings : ~[Binding<Ident>],
    pub constraints : ~[Constraint],
    pub typ : Type,
    pub classname : InternedStr
}

#[deriving(Clone, Eq)]
pub struct Binding<Ident = InternedStr> {
    pub name : Ident,
    pub arguments: ~[Pattern<Ident>],
    pub expression : TypedExpr<Ident>,
    pub typeDecl : TypeDeclaration,
    pub arity : uint
}

#[deriving(Eq, TotalEq, Clone, Show)]
pub struct Constructor<Ident = InternedStr> {
    pub name : Ident,
    pub typ : Type,
    pub tag : int,
    pub arity : int
}

#[deriving(Eq, Clone)]
pub struct DataDefinition<Ident = InternedStr> {
    pub constructors : ~[Constructor<Ident>],
    pub typ : Type,
    pub parameters : HashMap<InternedStr, int>
}

#[deriving(Clone, Eq, TotalEq, Default)]
pub struct TypeDeclaration {
    pub context : ~[Constraint],
    pub typ : Type,
    pub name : InternedStr
}

#[deriving(Clone, Default, Eq, TotalEq, Hash)]
pub struct TypeOperator {
    pub name : InternedStr,
    pub kind : Kind
}
#[deriving(Clone, Eq, TotalEq, Default)]
pub struct TypeVariable {
    pub id : int,
    pub kind : Kind
}
#[deriving(Clone, TotalEq, Hash)]
pub enum Type {
    TypeVariable(TypeVariable),
    TypeOperator(TypeOperator),
    TypeApplication(Box<Type>, Box<Type>),
    Generic(TypeVariable)
}

impl Type {

    pub fn new_var(id : int) -> Type {
        TypeVariable(TypeVariable { id : id, kind: unknown_kind.clone() })
    }
    pub fn new_var_args(id: int, types : ~[Type]) -> Type {
        let mut result = TypeVariable(TypeVariable { id : id, kind: Kind::new(types.len() as int + 1) });
        for typ in types.move_iter() {
            result = TypeApplication(box result, box typ);
        }
        result
    }
    pub fn new_var_kind(id : int, kind: Kind) -> Type {
        TypeVariable(TypeVariable { id : id, kind: kind })
    }
    pub fn new_op(name : InternedStr, types : ~[Type]) -> Type {
        let mut result = TypeOperator(TypeOperator { name : name, kind: Kind::new(types.len() as int + 1) });
        for typ in types.move_iter() {
            result = TypeApplication(box result, box typ);
        }
        result
    }
    pub fn new_op_kind(name : InternedStr, types : ~[Type], kind: Kind) -> Type {
        let mut result = TypeOperator(TypeOperator { name : name, kind: kind });
        for typ in types.move_iter() {
            result = TypeApplication(box result, box typ);
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

impl <S: Writer> ::std::hash::Hash<S> for TypeVariable {
    #[inline]
    fn hash(&self, state: &mut S) {
        self.id.hash(state);
    }
}

pub fn tuple_type(size: uint) -> (StrBuf, Type) {
    let mut var_list = Vec::new();
    for i in range(0, size) {
        var_list.push(Generic(Type::new_var_kind(i as int, star_kind.clone()).var().clone()));
    }
    let mut ident = StrBuf::from_char(1, '(');
    for _ in range(1, size) {
        ident.push_char(',');
    }
    ident.push_char(')');
    let mut typ = Type::new_op(intern(ident.as_slice()), FromVec::from_vec(var_list));
    for i in range_step(size as int - 1, -1, -1) {
        typ = function_type_(Generic(Type::new_var(i).var().clone()), typ);
    }
    (ident.into_owned(), typ)
}

pub fn list_type(typ: Type) -> Type {
    Type::new_op(intern("[]"), ~[typ])
}

pub fn char_type() -> Type {
    Type::new_op(intern("Char"), ~[])
}
pub fn int_type() -> Type {
    Type::new_op(intern("Int"), ~[])
}
pub fn bool_type() -> Type {
    Type::new_op(intern("Bool"), ~[])
}
pub fn double_type() -> Type {
    Type::new_op(intern("Double"), ~[])
}

pub fn function_type(func : &Type, arg : &Type) -> Type {
    Type::new_op(intern("->"), ~[func.clone(), arg.clone()])
}

pub fn function_type_(func : Type, arg : Type) -> Type {
    Type::new_op(intern("->"), ~[func, arg])
}

pub fn io(typ: Type) -> Type {
    Type::new_op(intern("IO"), ~[typ])
}
pub fn unit() -> Type {
    Type::new_op(intern("()"), ~[])
}


#[deriving(Clone, Eq, TotalEq, Hash)]
pub struct Constraint {
    pub class : InternedStr,
    pub variables : ~[TypeVariable]
}

#[deriving(Clone, Eq, TotalEq, Hash)]
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
        Type::new_var(-1)
    }
}
impl fmt::Show for TypeVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.id)
    }
}
impl fmt::Show for TypeOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[deriving(Eq, Ord)]
enum Prec_ {
    Top,
    Function,
    Constructor,
}
struct Prec<'a>(Prec_, &'a Type);

fn try_get_function<'a>(typ: &'a Type) -> Option<(&'a Type, &'a Type)> {
    match *typ {
        TypeApplication(ref xx, ref result) => {
            let y: &Type = *xx;
            match *y {
                TypeApplication(ref xx, ref arg) => {
                    let x: &Type = *xx;
                    match x {
                        &TypeOperator(ref op) if "->" == op.name.as_slice() => {
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
            TypeOperator(ref op) => write!(f, "{}", *op),
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
                            TypeOperator(ref op) if "[]" == op.name.as_slice() => {
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
impl fmt::Show for TypeDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{} :: ", self.name));
        for constraint in self.context.iter() {
            try!(write!(f, "{} ", *constraint));
        }
        if self.context.len() > 0 {
            try!(write!(f, "=> "));
        }
        write!(f, "{}", self.typ)
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


#[deriving(Clone)]
pub struct TypedExpr<Ident = InternedStr> {
    pub expr : Expr<Ident>,
    pub typ : Type,
    pub location : Location
}

impl <T: Eq> Eq for TypedExpr<T> {
    fn eq(&self, other : &TypedExpr<T>) -> bool {
        self.expr == other.expr
    }
}

impl <T: fmt::Show> fmt::Show for TypedExpr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.expr)
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

#[deriving(Clone, Eq)]
pub struct Alternative<Ident = InternedStr> {
    pub pattern : Located<Pattern<Ident>>,
    pub expression : TypedExpr<Ident>
}

#[deriving(Clone, Eq, TotalEq)]
pub enum Pattern<Ident = InternedStr> {
    NumberPattern(int),
    IdentifierPattern(Ident),
    ConstructorPattern(Ident, ~[Pattern<Ident>]),
    WildCardPattern
}

#[deriving(Clone, Eq)]
pub enum DoBinding<Ident = InternedStr> {
    DoLet(~[Binding<Ident>]),
    DoBind(Located<Pattern<Ident>>, TypedExpr<Ident>),
    DoExpr(TypedExpr<Ident>)
}

#[deriving(Clone, Eq)]
pub enum Literal {
    Integral(int),
    Fractional(f64),
    String(InternedStr),
    Char(char)
}
#[deriving(Clone, Eq)]
pub enum Expr<Ident = InternedStr> {
    Identifier(Ident),
    Apply(Box<TypedExpr<Ident>>, Box<TypedExpr<Ident>>),
    Literal(Literal),
    Lambda(Pattern<Ident>, Box<TypedExpr<Ident>>),
    Let(~[Binding<Ident>], Box<TypedExpr<Ident>>),
    Case(Box<TypedExpr<Ident>>, ~[Alternative<Ident>]),
    Do(~[DoBinding<Ident>], Box<TypedExpr<Ident>>)
}

impl <T: fmt::Show> fmt::Show for Expr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write_core_expr!(*self, f, _));
        match *self {
            Do(ref bindings, ref expr) => {
                try!(write!(f, "do \\{\n"));
                for bind in bindings.iter() {
                    match *bind {
                        DoLet(ref bindings) => {
                            try!(write!(f, "let \\{\n"));
                            for bind in bindings.iter() {
                                try!(write!(f, "; {} = {}\n", bind.name, bind.expression));
                            }
                            try!(write!(f, "\\}\n"));
                        }
                        DoBind(ref p, ref e) => try!(write!(f, "; {} <- {}\n", p.node, *e)),
                        DoExpr(ref e) => try!(write!(f, "; {}\n", *e))
                    }
                }
                write!(f, "{} \\}", *expr)
            }
            _ => Ok(())
        }
    }
}
impl <T: fmt::Show> fmt::Show for Pattern<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &IdentifierPattern(ref s) => write!(f, "{}", s),
            &NumberPattern(ref i) => write!(f, "{}", i),
            &ConstructorPattern(ref name, ref patterns) => {
                try!(write!(f, "({} ", name));
                for p in patterns.iter() {
                    try!(write!(f, " {}", p));
                }
                write!(f, ")")
            }
            &WildCardPattern => write!(f, "_")
        }
    }
}
impl fmt::Show for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Integral(i) => write!(f, "{}", i),
            Fractional(v) => write!(f, "{}", v),
            String(ref s) => write!(f, "\"{}\"", *s),
            Char(c) => write!(f, "'{}'", c)
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
        &Do(ref binds, ref expr) => {
            for bind in binds.iter() {
                match *bind {
                    DoLet(ref bs) => {
                        for b in bs.iter() {
                            visitor.visit_binding(b);
                        }
                    }
                    DoBind(ref pattern, ref e) => {
                        visitor.visit_pattern(&pattern.node);
                        visitor.visit_expr(e);
                    }
                    DoExpr(ref e) => visitor.visit_expr(e)
                }
            }
            visitor.visit_expr(*expr);
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
struct Binds<'a, Ident> {
    vec: &'a [Binding<Ident>]
}

impl <'a, Ident: Eq> Iterator<&'a [Binding<Ident>]> for Binds<'a, Ident> {
    fn next(&mut self) -> Option<&'a [Binding<Ident>]> {
        if self.vec.len() == 0 {
            None
        }
        else {
            let end = self.vec.iter()
                .position(|bind| bind.name != self.vec[0].name)
                .unwrap_or(self.vec.len());
            let head = self.vec.slice_to(end);
            self.vec = self.vec.slice_from(end);
            Some(head)
        }
    }
}

pub fn binding_groups<'a, Ident: Eq>(bindings: &'a [Binding<Ident>]) -> Binds<'a, Ident> {
    Binds { vec: bindings }
}

