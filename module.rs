use std::fmt;
use collections::HashMap;
use interner::{intern, InternedStr};
pub use std::default::Default;
pub use lexer::{Location, Located};
pub use types::*;

#[deriving(Clone)]
pub struct Module<Ident = InternedStr> {
    pub name : Ident,
    pub imports: ~[Import],
    pub bindings : ~[Binding<Ident>],
    pub typeDeclarations : ~[TypeDeclaration],
    pub classes : ~[Class],
    pub instances : ~[Instance<Ident>],
    pub dataDefinitions : ~[DataDefinition<Ident>],
    pub fixity_declarations : ~[FixityDeclaration<Ident>]
}

#[deriving(Clone)]
pub struct Import {
    pub module: InternedStr
}

#[deriving(Clone)]
pub struct Class<Ident = InternedStr> {
    pub constraints: ~[Constraint],
    pub name : Ident,
    pub variable : TypeVariable,
    pub declarations : ~[TypeDeclaration],
    pub bindings: ~[Binding]
}

#[deriving(Clone)]
pub struct Instance<Ident = InternedStr> {
    pub bindings : ~[Binding<Ident>],
    pub constraints : ~[Constraint],
    pub typ : Type,
    pub classname : InternedStr
}

#[deriving(Clone, PartialEq)]
pub struct Binding<Ident = InternedStr> {
    pub name : Ident,
    pub arguments: ~[Pattern<Ident>],
    pub matches: Match<Ident>,
    pub typ: Qualified<Type>
}

#[deriving(PartialEq, Eq, Clone, Show)]
pub struct Constructor<Ident = InternedStr> {
    pub name : Ident,
    pub typ : Qualified<Type>,
    pub tag : int,
    pub arity : int
}

#[deriving(PartialEq, Clone)]
pub struct DataDefinition<Ident = InternedStr> {
    pub constructors : ~[Constructor<Ident>],
    pub typ : Qualified<Type>,
    pub parameters : HashMap<InternedStr, int>
}

#[deriving(PartialEq, Clone, Show)]
pub enum Assoc {
    LeftAssoc,
    RightAssoc,
    NoAssoc
}

#[deriving(PartialEq, Clone, Show)]
pub struct FixityDeclaration<Ident = InternedStr> {
    pub assoc: Assoc,
    pub precedence: int,
    pub operators: ~[Ident]
}

#[deriving(Clone, PartialEq, Eq, Default)]
pub struct TypeDeclaration {
    pub typ : Qualified<Type>,
    pub name : InternedStr
}
impl fmt::Show for TypeDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} :: {}", self.name, self.typ)
    }
}


#[deriving(Clone)]
pub struct TypedExpr<Ident = InternedStr> {
    pub expr : Expr<Ident>,
    pub typ : Type,
    pub location : Location
}

impl <T: PartialEq> PartialEq for TypedExpr<T> {
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
        TypedExpr { expr : expr, typ : Type::new_var(intern("a")), location : Location { column : -1, row : -1, absolute : -1 } }
    }
    pub fn with_location<T>(expr : Expr<T>, loc : Location) -> TypedExpr<T> {
        TypedExpr { expr : expr, typ : Type::new_var(intern("a")), location : loc }
    }
}

#[deriving(Clone, PartialEq)]
pub struct Alternative<Ident = InternedStr> {
    pub pattern : Located<Pattern<Ident>>,
    pub matches: Match<Ident>,
}

#[deriving(Clone, PartialOrd, PartialEq, Eq)]
pub enum Pattern<Ident = InternedStr> {
    NumberPattern(int),
    IdentifierPattern(Ident),
    ConstructorPattern(Ident, ~[Pattern<Ident>]),
    WildCardPattern
}

#[deriving(Clone, PartialEq)]
pub enum Match<Ident = InternedStr> {
    Guards(~[Guard<Ident>]),
    Simple(TypedExpr<Ident>)
}
impl <Ident> Match<Ident> {
    pub fn location<'a>(&'a self) -> &'a Location {
        match *self {
            Guards(ref gs) => &gs[0].predicate.location,
            Simple(ref e) => &e.location
        }
    }
}

#[deriving(Clone, PartialEq, Show)]
pub struct Guard<Ident = InternedStr> {
    pub predicate: TypedExpr<Ident>,
    pub expression: TypedExpr<Ident>
}

#[deriving(Clone, PartialEq)]
pub enum DoBinding<Ident = InternedStr> {
    DoLet(~[Binding<Ident>]),
    DoBind(Located<Pattern<Ident>>, TypedExpr<Ident>),
    DoExpr(TypedExpr<Ident>)
}

#[deriving(Clone, PartialEq)]
pub enum Literal {
    Integral(int),
    Fractional(f64),
    String(InternedStr),
    Char(char)
}
#[deriving(Clone, PartialEq)]
pub enum Expr<Ident = InternedStr> {
    Identifier(Ident),
    Apply(Box<TypedExpr<Ident>>, Box<TypedExpr<Ident>>),
    OpApply(Box<TypedExpr<Ident>>, Ident, Box<TypedExpr<Ident>>),
    Literal(Literal),
    Lambda(Pattern<Ident>, Box<TypedExpr<Ident>>),
    Let(~[Binding<Ident>], Box<TypedExpr<Ident>>),
    Case(Box<TypedExpr<Ident>>, ~[Alternative<Ident>]),
    Do(~[DoBinding<Ident>], Box<TypedExpr<Ident>>),
    TypeSig(Box<TypedExpr<Ident>>, Qualified<Type>),
    Paren(Box<TypedExpr<Ident>>)
}
impl <T: fmt::Show> fmt::Show for Binding<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} = {}", self.name, self.matches)
    }
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
                                try!(write!(f, "; {} = {}\n", bind.name, bind.matches));
                            }
                            try!(write!(f, "\\}\n"));
                        }
                        DoBind(ref p, ref e) => try!(write!(f, "; {} <- {}\n", p.node, *e)),
                        DoExpr(ref e) => try!(write!(f, "; {}\n", *e))
                    }
                }
                write!(f, "{} \\}", *expr)
            }
            OpApply(ref lhs, ref op, ref rhs) => write!(f, "({} {} {})", lhs, op, rhs),
            TypeSig(ref expr, ref typ) => write!(f, "{} {}", expr, typ),
            Paren(ref expr) => write!(f, "({})", expr),
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

impl <T: fmt::Show> fmt::Show for Alternative<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} -> {}", self.pattern.node, self.matches)
    }
}
impl <T: fmt::Show> fmt::Show for Match<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Simple(ref e) => write!(f, "{}", *e),
            Guards(ref gs) => {
                for g in gs.iter() {
                    try!(write!(f, "| {} -> {}\n", g.predicate, g.expression));
                }
                Ok(())
            }
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

///Trait which implements the visitor pattern.
///The tree will be walked through automatically, calling the appropriate visit_ function
///If a visit_ function is overridden it will need to call the appropriate walk_function to
///recurse deeper into the AST
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
    match binding.matches {
        Simple(ref e) => visitor.visit_expr(e),
        _ => fail!()
    }
}

pub fn walk_expr<Ident>(visitor: &mut Visitor<Ident>, expr: &TypedExpr<Ident>) {
    match &expr.expr {
        &Apply(ref func, ref arg) => {
            visitor.visit_expr(*func);
            visitor.visit_expr(*arg);
        }
        &OpApply(ref lhs, ref op, ref rhs) => {
            visitor.visit_expr(*lhs);
            visitor.visit_expr(*rhs);
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
        &TypeSig(ref expr, _) => visitor.visit_expr(*expr),
        &Paren(ref expr) => visitor.visit_expr(*expr),
        &Literal(..) | &Identifier(..) => ()
    }
}

pub fn walk_alternative<Ident>(visitor: &mut Visitor<Ident>, alt: &Alternative<Ident>) {
    match alt.matches {
        Simple(ref e) => visitor.visit_expr(e),
        Guards(ref gs) => {
            for g in gs.iter() {
                visitor.visit_expr(&g.predicate);
                visitor.visit_expr(&g.expression);
            }
        }
    }
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



pub trait MutVisitor<Ident> {
    fn visit_expr(&mut self, expr: &mut TypedExpr<Ident>) {
        walk_expr_mut(self, expr)
    }
    fn visit_alternative(&mut self, alt: &mut Alternative<Ident>) {
        walk_alternative_mut(self, alt)
    }
    fn visit_pattern(&mut self, pattern: &mut Pattern<Ident>) {
        walk_pattern_mut(self, pattern)
    }
    fn visit_binding(&mut self, binding: &mut Binding<Ident>) {
        walk_binding_mut(self, binding);
    }
    fn visit_module(&mut self, module: &mut Module<Ident>) {
        walk_module_mut(self, module);
    }
}

pub fn walk_module_mut<Ident, V: MutVisitor<Ident>>(visitor: &mut V, module: &mut Module<Ident>) {
    for bind in module.instances.mut_iter().flat_map(|i| i.bindings.mut_iter()) {
        visitor.visit_binding(bind);
    }
    for bind in module.bindings.mut_iter() {
        visitor.visit_binding(bind);
    }
}

pub fn walk_binding_mut<Ident, V: MutVisitor<Ident>>(visitor: &mut V, binding: &mut Binding<Ident>) {
    match binding.matches {
        Simple(ref mut e) => visitor.visit_expr(e),
        Guards(ref mut gs) => {
            for g in gs.mut_iter() {
                visitor.visit_expr(&mut g.predicate);
                visitor.visit_expr(&mut g.expression);
            }
        }
    }
}

pub fn walk_expr_mut<Ident, V: MutVisitor<Ident>>(visitor: &mut V, expr: &mut TypedExpr<Ident>) {
    match expr.expr {
        Apply(ref mut func, ref mut arg) => {
            visitor.visit_expr(*func);
            visitor.visit_expr(*arg);
        }
        OpApply(ref mut lhs, _, ref mut rhs) => {
            visitor.visit_expr(*lhs);
            visitor.visit_expr(*rhs);
        }
        Lambda(_, ref mut body) => visitor.visit_expr(*body),
        Let(ref mut binds, ref mut e) => {
            for b in binds.mut_iter() {
                visitor.visit_binding(b);
            }
            visitor.visit_expr(*e);
        }
        Case(ref mut e, ref mut alts) => {
            visitor.visit_expr(*e);
            for alt in alts.mut_iter() {
                visitor.visit_alternative(alt);
            }
        }
        Do(ref mut binds, ref mut expr) => {
            for bind in binds.mut_iter() {
                match *bind {
                    DoLet(ref mut bs) => {
                        for b in bs.mut_iter() {
                            visitor.visit_binding(b);
                        }
                    }
                    DoBind(ref mut pattern, ref mut e) => {
                        visitor.visit_pattern(&mut pattern.node);
                        visitor.visit_expr(e);
                    }
                    DoExpr(ref mut e) => visitor.visit_expr(e)
                }
            }
            visitor.visit_expr(*expr);
        }
        TypeSig(ref mut expr, _) => visitor.visit_expr(*expr),
        Paren(ref mut expr) => visitor.visit_expr(*expr),
        Literal(..) | Identifier(..) => ()
    }
}

pub fn walk_alternative_mut<Ident, V: MutVisitor<Ident>>(visitor: &mut V, alt: &mut Alternative<Ident>) {
    match alt.matches {
        Simple(ref mut e) => visitor.visit_expr(e),
        Guards(ref mut gs) => {
            for g in gs.mut_iter() {
                visitor.visit_expr(&mut g.predicate);
                visitor.visit_expr(&mut g.expression);
            }
        }
    }
}

pub fn walk_pattern_mut<Ident, V: MutVisitor<Ident>>(visitor: &mut V, pattern: &mut Pattern<Ident>) {
    match pattern {
        &ConstructorPattern(_, ref mut ps) => {
            for p in ps.mut_iter() {
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

///Returns an iterator which returns slices which contain bindings which are next
///to eachother and have the same name.
///Ex
///not True = False
///not False = True
///undefined = ...
///Produces  [[not True, not False], [undefined]]
pub fn binding_groups<'a, Ident: Eq>(bindings: &'a [Binding<Ident>]) -> Binds<'a, Ident> {
    Binds { vec: bindings }
}

