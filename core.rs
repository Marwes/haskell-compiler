pub use module::{Type, TypeApplication, TypeOperator, TypeVariable, IdentifierPattern, ConstructorPattern, NumberPattern};
use module;

pub struct Module<Ident> {
    super_combinators: ~[Binding<Ident>]
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
pub struct Literal<Ident> {
    typ: Type,
    value: Literal_
}

#[deriving(Eq)]
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
    Literal(Literal<Ident>),
    Lambda(Ident, ~Expr<Ident>),
    Let(~[Binding<Ident>], ~Expr<Ident>),
    Case(~Expr<Ident>, ~[Alternative<Ident>])
}

pub trait Typed {
    fn get_type<'a>(&'a self) -> &'a Type;
}

impl Typed for (Type, ~str) {
    fn get_type<'a>(&'a self) -> &'a Type {
        self.ref0()
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

mod translate {
    use core::*;
    use module;

    pub fn translate(module: module::Module) -> Module<(Type, ~str)> {
        let module::Module { name : name,
            bindings : bindings,
            typeDeclarations : typeDeclarations,
            classes : classes,
            instances : instances,
            dataDefinitions : dataDefinitions
        } = module;
        let instance_functions = instances.move_iter().flat_map(|instance| {
            instance.bindings.move_iter().map(translate_binding)
        });
        let mut super_combinators = instance_functions.chain(bindings.move_iter().map(translate_binding)).collect();
        Module { super_combinators: super_combinators }
    }

    fn translate_binding(binding : module::Binding) -> Binding<(Type, ~str)> {
        let module::Binding { name: name, expression: expression, .. } = binding;
        let expr = translate_expression(expression);
        Binding { name: (expr.get_type().clone(), name), expression: expr }
    }
    fn translate_expression(input_expr: module::TypedExpr) -> Expr<(Type, ~str)> {
        let module::TypedExpr { typ: typ, expr: expr, ..} = input_expr;
        match expr {
            module::Identifier(s) => Identifier((typ, s)),
            module::Apply(func, arg) => Apply(~translate_expression(*func), ~translate_expression(*arg)),
            module::Number(num) => Literal(Literal { typ: typ, value: Integral(num) }),
            module::Rational(num) => Literal(Literal { typ: typ, value: Fractional(num) }),
            module::String(s) => Literal(Literal { typ: typ, value: String(s) }),
            module::Char(c) => Literal(Literal { typ: typ, value: Char(c) }),
            module::Lambda(arg, body) => Lambda((typ, arg), ~translate_expression(*body)),
            module::Let(bindings, body) => {
                let bs = bindings.move_iter().map(translate_binding).collect();
                Let(bs, ~translate_expression(*body))
            }
            module::Case(expr, alts) => {
                let a = alts.move_iter().map(|alt| {
                    let module::Alternative { pattern: pattern, expression: expression} = alt;
                    let p = translate_pattern(pattern.node);
                    Alternative { pattern: p, expression:translate_expression(expression) }
                }).collect();
                Case(~translate_expression(*expr), a)
            }
        }
    }
    fn translate_pattern(pattern: module::Pattern) -> Pattern<(Type, ~str)> {
        match pattern {
            IdentifierPattern(i) => IdentifierPattern((Type::new_var(0), i)),
            NumberPattern(n) => NumberPattern(n),
            ConstructorPattern(name, patterns) =>
                ConstructorPattern(name, patterns.move_iter().map(translate_pattern).collect())
        }
    }
}
