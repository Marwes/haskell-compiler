use std::fmt;
pub use module::{Type, TypeApplication, TypeOperator, TypeVariable, IdentifierPattern, ConstructorPattern, NumberPattern, Constraint, Class, DataDefinition, TypeDeclaration};
use module;

pub struct Module<Ident> {
    pub classes: ~[Class],
    pub data_definitions: ~[DataDefinition],
    pub instances: ~[(~[Constraint], Type)],
    pub bindings: ~[Binding<Ident>]
}

impl Module<(~[Constraint], Type, ~str)> {
    pub fn from_expr(expr: Expr<(~[Constraint], Type, ~str)>) -> Module<(~[Constraint], Type, ~str)> {
        Module {
            classes: ~[],
            data_definitions: ~[],
            instances: ~[],
            bindings: ~[Binding {
                name: (~[], expr.get_type().clone(), "main".to_owned()),
                expression: expr
            }]
        }
    }
}

#[deriving(Eq)]
pub struct Binding<Ident> {
    pub name: Ident,
    pub expression: Expr<Ident>
}

#[deriving(Eq)]
pub struct Alternative<Ident> {
    pub pattern : Pattern<Ident>,
    pub expression : Expr<Ident>
}

pub type Pattern<Ident> = module::Pattern<Ident>;

#[deriving(Eq)]
pub struct Literal {
    pub typ: Type,
    pub value: Literal_
}

#[deriving(Eq, Show)]
pub enum Literal_ {
    Integral(int),
    Fractional(f64),
    String(~str),
    Char(char)
}

#[deriving(Eq)]
pub enum Expr<Ident> {
    Identifier(Ident),
    Apply(~Expr<Ident>, ~Expr<Ident>),
    Literal(Literal),
    Lambda(Ident, ~Expr<Ident>),
    Let(~[Binding<Ident>], ~Expr<Ident>),
    Case(~Expr<Ident>, ~[Alternative<Ident>])
}

impl <T: fmt::Show> fmt::Show for Expr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Identifier(ref s) => write!(f.buf, "{}", s),
            &Apply(ref func, ref arg) => write!(f.buf, "({} {})", *func, *arg),
            &Literal(ref literal) => {
                match &literal.value {
                    &Integral(i) => write!(f.buf, "{}", i),
                    &Fractional(i) => write!(f.buf, "{}", i),
                    &String(ref i) => write!(f.buf, "{}", i),
                    &Char(i) => write!(f.buf, "{}", i)
                }
            }
            &Lambda(ref arg, ref body) => write!(f.buf, "(\\\\{} -> {})", arg, *body),
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
                    try!(write!(f.buf, "; {} -> {}\n", alt.pattern, alt.expression));
                }
                write!(f.buf, "\\}\n")
            }
        }
    }
}

pub trait Typed {
    fn get_type<'a>(&'a self) -> &'a Type;
}

impl Typed for (~[Constraint], Type, ~str) {
    fn get_type<'a>(&'a self) -> &'a Type {
        self.ref1()
    }
}

impl <Ident: Typed> Typed for Expr<Ident> {
    fn get_type<'a>(&'a self) -> &'a Type {
        match self {
            &Identifier(ref i) => i.get_type(),
            &Literal(ref lit) => &lit.typ,
            &Apply(ref func, _) => {
                match func.get_type() {
                    &TypeApplication(_, ref a) => { let a2: &Type = *a; a2 }
                    _ => fail!("The function in Apply must be a type application")
                }
            }
            &Lambda(ref arg, _) => arg.get_type(),
            &Let(_, ref body) => body.get_type(),
            &Case(_, ref alts) => alts[0].expression.get_type()
        }
    }
}

#[deriving(Eq, TotalEq, Hash, Clone, Show)]
pub struct Name {
    pub name: ~str,
    pub uid: uint
}

impl <'a> Equiv<&'a str> for Name {
    fn equiv(&self, o: & &str) -> bool {
        *o == self.name
    }
}

#[deriving(Eq, TotalEq, Hash, Clone)]
pub struct Id {
    pub name: Name,
    pub typ: Type,
    pub constraints: ~[Constraint]
}

impl fmt::Show for Id {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f.buf, "{}_{}", self.name.name, self.name.uid)
    }
}

impl Id {
    pub fn new(name: Name, typ: Type, constraints: ~[Constraint]) -> Id {
        Id { name: name, typ: typ, constraints: constraints }
    }
}

impl Str for Id {
    fn as_slice<'a>(&'a self) -> &'a str {
        self.name.name.as_slice()
    }
    fn into_owned(self) -> ~str {
        self.name.name
    }
}

impl Typed for Id {
    fn get_type<'a>(&'a self) -> &'a Type {
        &self.typ
    }
}


pub trait Visitor<Ident> {
    fn visit_expr(&mut self, expr: &Expr<Ident>) {
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
    for bind in module.bindings.iter() {
        visitor.visit_binding(bind);
    }
}

pub fn walk_binding<Ident>(visitor: &mut Visitor<Ident>, binding: &Binding<Ident>) {
    visitor.visit_expr(&binding.expression);
}

pub fn walk_expr<Ident>(visitor: &mut Visitor<Ident>, expr: &Expr<Ident>) {
    match expr {
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

pub mod translate {
    use core::*;
    use module;
        
    pub fn translate_module(module: module::Module) -> Module<(~[Constraint], Type, ~str)> {
        let module::Module { name : _name,
            bindings : bindings,
            typeDeclarations : _typeDeclarations,
            classes : classes,
            instances : instances,
            dataDefinitions : dataDefinitions
        } = module;
        let mut instance_functions = Vec::new();
        let mut new_instances = Vec::new();
        for module::Instance {classname: classname, typ: typ, constraints: constraints, bindings: bindings } in instances.move_iter() {
            new_instances.push((constraints.clone(), Type::new_op(classname, ~[typ])));
            instance_functions.extend(bindings.move_iter().map(translate_binding));
        }
        instance_functions.extend(bindings.move_iter().map(translate_binding));
        Module {
            classes: classes,
            data_definitions: dataDefinitions,
            bindings: instance_functions.move_iter().collect(),
            instances: new_instances.move_iter().collect()
        }
    }

    pub fn translate_expr(input_expr: module::TypedExpr) -> Expr<(~[Constraint], Type, ~str)> {
        //Checks if the expression is lambda not bound by a let binding
        //if it is then we wrap the lambda in a let binding
        let is_lambda = match &input_expr.expr {
            &module::Lambda(_, _) => true,
            _ => false
        };
        if is_lambda {
            let module::TypedExpr { typ: typ, expr: expr, ..} = input_expr;
            match expr {
                module::Lambda(arg, body) => {
                    let l = Lambda((~[], typ.clone(), arg.clone()), ~translate_expr_rest(*body));
                    let bind = Binding { name: (~[], typ.clone(), "#lambda".to_owned()), expression: l };
                    Let(~[bind], ~Identifier((~[], typ, "#lambda".to_owned())))
                }
                _ => fail!()
            }
        }
        else {
            translate_expr_rest(input_expr)
        }
    }

    fn translate_expr_rest(input_expr: module::TypedExpr) -> Expr<(~[Constraint], Type, ~str)> {
        let module::TypedExpr { typ: typ, expr: expr, ..} = input_expr;
        match expr {
            module::Identifier(s) => Identifier((~[], typ, s)),
            module::Apply(func, arg) => Apply(~translate_expr(*func), ~translate_expr(*arg)),
            module::Number(num) => Literal(Literal { typ: typ, value: Integral(num) }),
            module::Rational(num) => Literal(Literal { typ: typ, value: Fractional(num) }),
            module::String(s) => Literal(Literal { typ: typ, value: String(s) }),
            module::Char(c) => Literal(Literal { typ: typ, value: Char(c) }),
            module::Lambda(arg, body) => Lambda((~[], typ, arg), ~translate_expr_rest(*body)),
            module::Let(bindings, body) => {
                let bs = bindings.move_iter().map(translate_binding).collect();
                Let(bs, ~translate_expr(*body))
            }
            module::Case(expr, alts) => {
                let a = alts.move_iter().map(|alt| {
                    let module::Alternative { pattern: pattern, expression: expr} = alt;
                    let p = translate_pattern(pattern.node);
                    Alternative { pattern: p, expression:translate_expr(expr) }
                }).collect();
                Case(~translate_expr(*expr), a)
            }
        }
    }

    fn translate_binding(binding : module::Binding) -> Binding<(~[Constraint], Type, ~str)> {
        let module::Binding { name: name, expression: expr, typeDecl: typeDecl, .. } = binding;
        let expr = translate_expr_rest(expr);
        Binding { name: (typeDecl.context, expr.get_type().clone(), name), expression: expr }
    }
    
    fn translate_pattern(pattern: module::Pattern) -> Pattern<(~[Constraint], Type, ~str)> {
        match pattern {
            IdentifierPattern(i) => IdentifierPattern((~[], Type::new_var(0), i)),
            NumberPattern(n) => NumberPattern(n),
            ConstructorPattern(name, patterns) =>
                ConstructorPattern(name, patterns.move_iter().map(translate_pattern).collect())
        }
    }
}
