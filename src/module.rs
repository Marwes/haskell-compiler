use std::fmt;
use std::collections::HashMap;
use crate::interner::{intern, InternedStr};
use crate::lexer::{Location, Located};
pub use std::default::Default;
pub use crate::types::*;

use self::Expr::*;

#[derive(Clone, Debug)]
pub struct Module<Ident = InternedStr> {
    pub name : Ident,
    pub imports: Vec<Import<Ident>>,
    pub bindings : Vec<Binding<Ident>>,
    pub type_declarations : Vec<TypeDeclaration<Ident>>,
    pub classes : Vec<Class<Ident>>,
    pub instances : Vec<Instance<Ident>>,
    pub data_definitions : Vec<DataDefinition<Ident>>,
    pub newtypes : Vec<Newtype<Ident>>,
    pub fixity_declarations : Vec<FixityDeclaration<Ident>>
}

#[derive(Clone, Debug)]
pub struct Import<Ident> {
    pub module: InternedStr,
    //None if 'import Name'
    //Some(names) if 'import Name (names)'
    pub imports: Option<Vec<Ident>>
}

#[derive(Clone, Debug)]
pub struct Class<Ident = InternedStr> {
    pub constraints: Vec<Constraint<Ident>>,
    pub name : Ident,
    pub variable : TypeVariable,
    pub declarations : Vec<TypeDeclaration<Ident>>,
    pub bindings: Vec<Binding<Ident>>
}

#[derive(Clone, Debug)]
pub struct Instance<Ident = InternedStr> {
    pub bindings : Vec<Binding<Ident>>,
    pub constraints : Vec<Constraint<Ident>>,
    pub typ : Type<Ident>,
    pub classname : Ident
}

#[derive(Clone, Debug, PartialEq)]
pub struct Binding<Ident = InternedStr> {
    pub name : Ident,
    pub arguments: Vec<Pattern<Ident>>,
    pub matches: Match<Ident>,
    pub where_bindings : Option<Vec<Binding<Ident>>>,
    pub typ: Qualified<Type<Ident>, Ident>
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Constructor<Ident = InternedStr> {
    pub name : Ident,
    pub typ : Qualified<Type<Ident>, Ident>,
    pub tag : isize,
    pub arity : isize
}

#[derive(PartialEq, Clone, Debug)]
pub struct DataDefinition<Ident = InternedStr> {
    pub constructors : Vec<Constructor<Ident>>,
    pub typ : Qualified<Type<Ident>, Ident>,
    pub parameters : HashMap<InternedStr, isize>,
    pub deriving: Vec<Ident>
}

#[derive(PartialEq, Clone, Debug)]
pub struct Newtype<Ident = InternedStr> {
    pub typ: Qualified<Type>,
    pub constructor_name: Ident,
    pub constructor_type: Qualified<Type<Ident>, Ident>,
    pub deriving: Vec<Ident>
}

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum Assoc {
    Left,
    Right,
    No
}

#[derive(PartialEq, Clone, Debug)]
pub struct FixityDeclaration<Ident = InternedStr> {
    pub assoc: Assoc,
    pub precedence: isize,
    pub operators: Vec<Ident>
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct TypeDeclaration<Ident = InternedStr> {
    pub typ : Qualified<Type<Ident>, Ident>,
    pub name : Ident
}
impl <T : fmt::Display + AsRef<str>> fmt::Display for TypeDeclaration<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} :: {}", self.name, self.typ)
    }
}


#[derive(Clone, Debug)]
pub struct TypedExpr<Ident = InternedStr> {
    pub expr : Expr<Ident>,
    pub typ : Type<Ident>,
    pub location : Location
}

impl <T: PartialEq> PartialEq for TypedExpr<T> {
    fn eq(&self, other : &TypedExpr<T>) -> bool {
        self.expr == other.expr
    }
}

impl <T: fmt::Display + AsRef<str>> fmt::Display for TypedExpr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} :: {}", self.expr, self.typ)
    }
}

impl TypedExpr {
    pub fn new<T: fmt::Display + AsRef<str>>(expr : Expr<T>) -> TypedExpr<T> {
        TypedExpr { expr : expr, typ : Type::new_var(intern("a")), location : Location { column : -1, row : -1, absolute : -1 } }
    }
    pub fn with_location<T: fmt::Display + AsRef<str>>(expr : Expr<T>, loc : Location) -> TypedExpr<T> {
        TypedExpr { expr : expr, typ : Type::new_var(intern("a")), location : loc }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Alternative<Ident = InternedStr> {
    pub pattern : Located<Pattern<Ident>>,
    pub matches: Match<Ident>,
    pub where_bindings : Option<Vec<Binding<Ident>>>
}

#[derive(Clone, Debug, PartialOrd, PartialEq, Eq)]
pub enum Pattern<Ident = InternedStr> {
    Number(isize),
    Identifier(Ident),
    Constructor(Ident, Vec<Pattern<Ident>>),
    WildCard
}

#[derive(Clone, Debug, PartialEq)]
pub enum Match<Ident = InternedStr> {
    Guards(Vec<Guard<Ident>>),
    Simple(TypedExpr<Ident>)
}
impl <Ident> Match<Ident> {
    pub fn location<'a>(&'a self) -> &'a Location {
        match *self {
            Match::Guards(ref gs) => &gs[0].predicate.location,
            Match::Simple(ref e) => &e.location
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Guard<Ident = InternedStr> {
    pub predicate: TypedExpr<Ident>,
    pub expression: TypedExpr<Ident>
}

#[derive(Clone, Debug, PartialEq)]
pub enum DoBinding<Ident = InternedStr> {
    DoLet(Vec<Binding<Ident>>),
    DoBind(Located<Pattern<Ident>>, TypedExpr<Ident>),
    DoExpr(TypedExpr<Ident>)
}

#[derive(Clone, Debug, PartialEq)]
pub enum LiteralData {
    Integral(isize),
    Fractional(f64),
    String(InternedStr),
    Char(char)
}
#[derive(Clone, Debug, PartialEq)]
pub enum Expr<Ident = InternedStr> {
    Identifier(Ident),
    Apply(Box<TypedExpr<Ident>>, Box<TypedExpr<Ident>>),
    OpApply(Box<TypedExpr<Ident>>, Ident, Box<TypedExpr<Ident>>),
    Literal(LiteralData),
    Lambda(Pattern<Ident>, Box<TypedExpr<Ident>>),
    Let(Vec<Binding<Ident>>, Box<TypedExpr<Ident>>),
    Case(Box<TypedExpr<Ident>>, Vec<Alternative<Ident>>),
    IfElse(Box<TypedExpr<Ident>>, Box<TypedExpr<Ident>>, Box<TypedExpr<Ident>>),
    Do(Vec<DoBinding<Ident>>, Box<TypedExpr<Ident>>),
    TypeSig(Box<TypedExpr<Ident>>, Qualified<Type<Ident>, Ident>),
    Paren(Box<TypedExpr<Ident>>)
}
impl <T: fmt::Display + AsRef<str>> fmt::Display for Binding<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} = {}", self.name, self.matches)
    }
}

impl <T: fmt::Display + AsRef<str>> fmt::Display for Expr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write_core_expr!(*self, f, _)?;
        match *self {
            Do(ref bindings, ref expr) => {
                write!(f, "do {{\n")?;
                for bind in bindings.iter() {
                    match *bind {
                        DoBinding::DoLet(ref bindings) => {
                            write!(f, "let {{\n")?;
                            for bind in bindings.iter() {
                                write!(f, "; {} = {}\n", bind.name, bind.matches)?;
                            }
                            write!(f, "}}\n")?;
                        }
                        DoBinding::DoBind(ref p, ref e) => write!(f, "; {} <- {}\n", p.node, *e)?,
                        DoBinding::DoExpr(ref e) => write!(f, "; {}\n", *e)?
                    }
                }
                write!(f, "{} }}", *expr)
            }
            OpApply(ref lhs, ref op, ref rhs) => write!(f, "({} {} {})", lhs, op, rhs),
            TypeSig(ref expr, ref typ) => write!(f, "{} {}", expr, typ),
            Paren(ref expr) => write!(f, "({})", expr),
            _ => Ok(())
        }
    }
}
impl <T: fmt::Display + AsRef<str>> fmt::Display for Pattern<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Pattern::Identifier(ref s) => write!(f, "{}", s),
            &Pattern::Number(ref i) => write!(f, "{}", i),
            &Pattern::Constructor(ref name, ref patterns) => {
                write!(f, "({} ", name)?;
                for p in patterns.iter() {
                    write!(f, " {}", p)?;
                }
                write!(f, ")")
            }
            &Pattern::WildCard => write!(f, "_")
        }
    }
}

impl <T: fmt::Display + AsRef<str>> fmt::Display for Alternative<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} -> {}", self.pattern.node, self.matches)
    }
}
impl <T: fmt::Display + AsRef<str>> fmt::Display for Match<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Match::Simple(ref e) => write!(f, "{}", *e),
            Match::Guards(ref gs) => {
                for g in gs.iter() {
                    write!(f, "| {} -> {}\n", g.predicate, g.expression)?;
                }
                Ok(())
            }
        }
    }
}
impl fmt::Display for LiteralData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            LiteralData::Integral(i) => write!(f, "{}", i),
            LiteralData::Fractional(v) => write!(f, "{}", v),
            LiteralData::String(ref s) => write!(f, "\"{}\"", *s),
            LiteralData::Char(c) => write!(f, "'{}'", c)
        }
    }
}

///Trait which implements the visitor pattern.
///The tree will be walked through automatically, calling the appropriate visit_ function
///If a visit_ function is overridden it will need to call the appropriate walk_function to
///recurse deeper into the AST
pub trait Visitor<Ident> : Sized {
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

pub fn walk_module<Ident, V: Visitor<Ident>>(visitor: &mut V, module: &Module<Ident>) {
    for bind in module.instances.iter().flat_map(|i| i.bindings.iter()) {
        visitor.visit_binding(bind);
    }
    for bind in module.bindings.iter() {
        visitor.visit_binding(bind);
    }
}

pub fn walk_binding<Ident, V: Visitor<Ident>>(visitor: &mut V, binding: &Binding<Ident>) {
    match binding.matches {
        Match::Simple(ref e) => visitor.visit_expr(e),
        _ => panic!()
    }
}

pub fn walk_expr<Ident, V: Visitor<Ident>>(visitor: &mut V, expr: &TypedExpr<Ident>) {
    match &expr.expr {
        &Apply(ref func, ref arg) => {
            visitor.visit_expr(&**func);
            visitor.visit_expr(&**arg);
        }
        &OpApply(ref lhs, _, ref rhs) => {
            visitor.visit_expr(&**lhs);
            visitor.visit_expr(&**rhs);
        }
        &Lambda(_, ref body) => visitor.visit_expr(&**body),
        &Let(ref binds, ref e) => {
            for b in binds.iter() {
                visitor.visit_binding(b);
            }
            visitor.visit_expr(&**e);
        }
        &Case(ref e, ref alts) => {
            visitor.visit_expr(&**e);
            for alt in alts.iter() {
                visitor.visit_alternative(alt);
            }
        }
        &IfElse(ref pred, ref if_true, ref if_false) => {
            visitor.visit_expr(&**pred);
            visitor.visit_expr(&**if_true);
            visitor.visit_expr(&**if_false);
        }
        &Do(ref binds, ref expr) => {
            for bind in binds.iter() {
                match *bind {
                    DoBinding::DoLet(ref bs) => {
                        for b in bs.iter() {
                            visitor.visit_binding(b);
                        }
                    }
                    DoBinding::DoBind(ref pattern, ref e) => {
                        visitor.visit_pattern(&pattern.node);
                        visitor.visit_expr(e);
                    }
                    DoBinding::DoExpr(ref e) => visitor.visit_expr(e)
                }
            }
            visitor.visit_expr(&**expr);
        }
        &TypeSig(ref expr, _) => visitor.visit_expr(&**expr),
        &Paren(ref expr) => visitor.visit_expr(&**expr),
        &Literal(..) | &Identifier(..) => ()
    }
}

pub fn walk_alternative<Ident, V: Visitor<Ident>>(visitor: &mut V, alt: &Alternative<Ident>) {
    visitor.visit_pattern(&alt.pattern.node);
    match alt.matches {
        Match::Simple(ref e) => visitor.visit_expr(e),
        Match::Guards(ref gs) => {
            for g in gs.iter() {
                visitor.visit_expr(&g.predicate);
                visitor.visit_expr(&g.expression);
            }
        }
    }
    match alt.where_bindings {
        Some(ref bindings) => {
            for bind in bindings.iter() {
                visitor.visit_binding(bind);
            }
        }
        None => ()
    }
}

pub fn walk_pattern<Ident, V: Visitor<Ident>>(visitor: &mut V, pattern: &Pattern<Ident>) {
    match pattern {
        &Pattern::Constructor(_, ref ps) => {
            for p in ps.iter() {
                visitor.visit_pattern(p);
            }
        }
        _ => ()
    }
}



pub trait MutVisitor<Ident> : Sized {
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
    for bind in module.instances.iter_mut().flat_map(|i| i.bindings.iter_mut()) {
        visitor.visit_binding(bind);
    }
    for bind in module.bindings.iter_mut() {
        visitor.visit_binding(bind);
    }
}

pub fn walk_binding_mut<Ident, V: MutVisitor<Ident>>(visitor: &mut V, binding: &mut Binding<Ident>) {
    match binding.matches {
        Match::Simple(ref mut e) => visitor.visit_expr(e),
        Match::Guards(ref mut gs) => {
            for g in gs.iter_mut() {
                visitor.visit_expr(&mut g.predicate);
                visitor.visit_expr(&mut g.expression);
            }
        }
    }
}

pub fn walk_expr_mut<Ident, V: MutVisitor<Ident>>(visitor: &mut V, expr: &mut TypedExpr<Ident>) {
    match expr.expr {
        Apply(ref mut func, ref mut arg) => {
            visitor.visit_expr(&mut **func);
            visitor.visit_expr(&mut **arg);
        }
        OpApply(ref mut lhs, _, ref mut rhs) => {
            visitor.visit_expr(&mut **lhs);
            visitor.visit_expr(&mut **rhs);
        }
        Lambda(_, ref mut body) => visitor.visit_expr(&mut **body),
        Let(ref mut binds, ref mut e) => {
            for b in binds.iter_mut() {
                visitor.visit_binding(b);
            }
            visitor.visit_expr(&mut **e);
        }
        Case(ref mut e, ref mut alts) => {
            visitor.visit_expr(&mut **e);
            for alt in alts.iter_mut() {
                visitor.visit_alternative(alt);
            }
        }
        IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
            visitor.visit_expr(&mut **pred);
            visitor.visit_expr(&mut **if_true);
            visitor.visit_expr(&mut **if_false);
        }
        Do(ref mut binds, ref mut expr) => {
            for bind in binds.iter_mut() {
                match *bind {
                    DoBinding::DoLet(ref mut bs) => {
                        for b in bs.iter_mut() {
                            visitor.visit_binding(b);
                        }
                    }
                    DoBinding::DoBind(ref mut pattern, ref mut e) => {
                        visitor.visit_pattern(&mut pattern.node);
                        visitor.visit_expr(e);
                    }
                    DoBinding::DoExpr(ref mut e) => visitor.visit_expr(e)
                }
            }
            visitor.visit_expr(&mut **expr);
        }
        TypeSig(ref mut expr, _) => visitor.visit_expr(&mut **expr),
        Paren(ref mut expr) => visitor.visit_expr(&mut **expr),
        Literal(..) | Identifier(..) => ()
    }
}

pub fn walk_alternative_mut<Ident, V: MutVisitor<Ident>>(visitor: &mut V, alt: &mut Alternative<Ident>) {
    visitor.visit_pattern(&mut alt.pattern.node);
    match alt.matches {
        Match::Simple(ref mut e) => visitor.visit_expr(e),
        Match::Guards(ref mut gs) => {
            for g in gs.iter_mut() {
                visitor.visit_expr(&mut g.predicate);
                visitor.visit_expr(&mut g.expression);
            }
        }
    }
    match alt.where_bindings {
        Some(ref mut bindings) => {
            for bind in bindings.iter_mut() {
                visitor.visit_binding(bind);
            }
        }
        None => ()
    }
}

pub fn walk_pattern_mut<Ident, V: MutVisitor<Ident>>(visitor: &mut V, pattern: &mut Pattern<Ident>) {
    match *pattern {
        Pattern::Constructor(_, ref mut ps) => {
            for p in ps.iter_mut() {
                visitor.visit_pattern(p);
            }
        }
        _ => ()
    }
}

pub struct Binds<'a, Ident: 'a> {
    vec: &'a [Binding<Ident>]
}


impl <'a, Ident: Eq> Iterator for Binds<'a, Ident> {
    type Item = &'a [Binding<Ident>];
    fn next(&mut self) -> Option<&'a [Binding<Ident>]> {
        if self.vec.len() == 0 {
            None
        }
        else {
            let end = self.vec.iter()
                .position(|bind| bind.name != self.vec[0].name)
                .unwrap_or(self.vec.len());
            let head = &self.vec[..end];
            self.vec = &self.vec[end..];
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

///Since bindings in instances have the same name as any other instance for the same class we
///Give it a new name which is '# Type name' (no spaces)
pub fn encode_binding_identifier(instancename : InternedStr, bindingname : InternedStr) -> InternedStr {
    let mut buffer = String::new();
    buffer.push_str("#");
    buffer.push_str(&instancename);
    buffer.push_str(&bindingname);
    intern(buffer.as_ref())
}

