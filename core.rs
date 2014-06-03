use std::fmt;
pub use module::{Type, TypeApplication, TypeOperator, TypeVariable, Match, Simple, IdentifierPattern, ConstructorPattern, WildCardPattern, NumberPattern, Constraint, Class, DataDefinition, TypeDeclaration, function_type_, Integral, Fractional, String, Char};
use module;
use interner::*;
pub use renamer::Name;

pub struct Module<Ident> {
    pub classes: ~[Class],
    pub data_definitions: ~[DataDefinition<Name>],
    pub instances: ~[(~[Constraint], Type)],
    pub bindings: ~[Binding<Ident>]
}

impl Module<Id> {
    pub fn from_expr(expr: Expr<Id>) -> Module<Id> {
        Module {
            classes: ~[],
            data_definitions: ~[],
            instances: ~[],
            bindings: ~[Binding {
                name: Id::new(Name { name: intern("main"), uid: 0 }, expr.get_type().clone(), ~[]),
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

pub type Literal_ = module::Literal;

#[deriving(Eq)]
pub enum Expr<Ident> {
    Identifier(Ident),
    Apply(Box<Expr<Ident>>, Box<Expr<Ident>>),
    Literal(Literal),
    Lambda(Ident, Box<Expr<Ident>>),
    Let(~[Binding<Ident>], Box<Expr<Ident>>),
    Case(Box<Expr<Ident>>, ~[Alternative<Ident>])
}

impl fmt::Show for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl <T: fmt::Show> fmt::Show for Binding<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} = {}", self.name, self.expression)
    }
}

impl <T: fmt::Show> fmt::Show for Expr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write_core_expr!(*self, f,)
    }
}

pub trait Typed {
    fn get_type<'a>(&'a self) -> &'a Type;
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

impl <'a> Equiv<&'a str> for Name {
    fn equiv(&self, o: & &str) -> bool {
        self.name == intern(*o)
    }
}

#[deriving(Eq, TotalEq, Hash, Clone)]
pub struct Id<T = Name> {
    pub name: T,
    pub typ: Type,
    pub constraints: ~[Constraint]
}

impl fmt::Show for Id {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl <T> Id<T> {
    pub fn new(name: T, typ: Type, constraints: ~[Constraint]) -> Id<T> {
        Id { name: name, typ: typ, constraints: constraints }
    }
}

impl Str for Id {
    fn as_slice<'a>(&'a self) -> &'a str {
        self.name.name.as_slice()
    }
}

impl <T> Typed for Id<T> {
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

pub mod result {
    use core::*;
    use std::vec::FromVec;

    pub trait Visitor<Ident> {
        fn visit_expr(&mut self, expr: Expr<Ident>) -> Expr<Ident> {
            walk_expr(self, expr)
        }
        fn visit_alternative(&mut self, alt: Alternative<Ident>) -> Alternative<Ident> {
            walk_alternative(self, alt)
        }
        fn visit_pattern(&mut self, pattern: Pattern<Ident>) -> Pattern<Ident> {
            walk_pattern(self, pattern)
        }
        fn visit_binding(&mut self, binding: Binding<Ident>) -> Binding<Ident> {
            walk_binding(self, binding)
        }
        fn visit_module(&mut self, module: Module<Ident>) -> Module<Ident> {
            walk_module(self, module)
        }
    }

    pub fn walk_module<Ident>(visitor: &mut Visitor<Ident>, mut module: Module<Ident>) -> Module<Ident> {
        let mut bindings = ~[];
        ::std::mem::swap(&mut module.bindings, &mut bindings);
        module.bindings = FromVec::<Binding<Ident>>::from_vec(bindings.move_iter()
            .map(|bind| visitor.visit_binding(bind))
            .collect());
        module
    }

    pub fn walk_binding<Ident>(visitor: &mut Visitor<Ident>, binding: Binding<Ident>) -> Binding<Ident> {
        let Binding { name: name, expression: expression } = binding;
        Binding {
            name: name,
            expression: visitor.visit_expr(expression)
        }
    }

    pub fn walk_expr<Ident>(visitor: &mut Visitor<Ident>, expr: Expr<Ident>) -> Expr<Ident> {
        match expr {
            Apply(func, arg) => {
                let f = visitor.visit_expr(*func);
                let a = visitor.visit_expr(*arg);
                Apply(box f, box a)
            }
            Lambda(x, body) => Lambda(x, box visitor.visit_expr(*body)),
            Let(binds, e) => {
                let bs: Vec<Binding<Ident>> = binds.move_iter().map(|b| {
                    visitor.visit_binding(b)
                }).collect();
                Let(FromVec::from_vec(bs), box visitor.visit_expr(*e))
            }
            Case(e, alts) => {
                let e2 = visitor.visit_expr(*e);
                let alts2: Vec<Alternative<Ident>> = alts.move_iter()
                    .map(|alt| visitor.visit_alternative(alt))
                    .collect();
                Case(box e2, FromVec::from_vec(alts2))
            }
            expr => expr
        }
    }

    pub fn walk_alternative<Ident>(visitor: &mut Visitor<Ident>, alt: Alternative<Ident>) -> Alternative<Ident> {
        let Alternative { pattern: pattern, expression: expression } = alt;
        Alternative { pattern: visitor.visit_pattern(pattern), expression: visitor.visit_expr(expression) }
    }

    pub fn walk_pattern<Ident>(visitor: &mut Visitor<Ident>, pattern: Pattern<Ident>) -> Pattern<Ident> {
        match pattern {
            ConstructorPattern(x, ps) => {
                let ps2: Vec<Pattern<Ident>> = ps.move_iter().map(|p| {
                    visitor.visit_pattern(p)
                }).collect();
                ConstructorPattern(x, FromVec::from_vec(ps2))
            }
            _ => pattern
        }
    }
}

pub mod translate {
    use module;
    use module::{function_type_, char_type, list_type};
    use core::*;
    use interner::*;
    use std::vec::FromVec;
        
    pub fn translate_module(module: module::Module<Name>) -> Module<Id<Name>> {
        let module::Module { name : _name,
            imports : _imports,
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
            instance_functions.extend(translate_bindings(bindings).move_iter());
        }
        instance_functions.extend(translate_bindings(bindings).move_iter());
        Module {
            classes: classes,
            data_definitions: dataDefinitions,
            bindings: FromVec::from_vec(instance_functions),
            instances: FromVec::from_vec(new_instances)
        }
    }

    fn translate_match(matches: module::Match<Name>) -> Expr<Id<Name>> {
        match matches {
            Simple(e) => translate_expr(e),
            _ => fail!()
        }
    }

    pub fn translate_expr(input_expr: module::TypedExpr<Name>) -> Expr<Id<Name>> {
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
                    //TODO need to make unique names for the lambdas created here
                    let argname = match arg {
                        IdentifierPattern(arg) => arg,
                        WildCardPattern => Name { name: intern("_"), uid: -1 },
                        _ => fail!("Core translation of pattern matches in lambdas are not implemented")
                    };
                    let l = Lambda(Id::new(argname, typ.clone(), ~[]), box translate_expr_rest(*body));
                    let bind = Binding { name: Id::new(Name { name: intern("#lambda"), uid: 0 }, typ.clone(), ~[]), expression: l };
                    Let(~[bind], box Identifier(Id::new(Name { name: intern("#lambda"), uid: 0 }, typ.clone(), ~[])))
                }
                _ => fail!()
            }
        }
        else {
            translate_expr_rest(input_expr)
        }
    }

    fn translate_expr_rest(input_expr: module::TypedExpr<Name>) -> Expr<Id<Name>> {
        let module::TypedExpr { typ: typ, expr: expr, ..} = input_expr;
        match expr {
            module::Identifier(s) => Identifier(Id::new(s, typ, ~[])),
            module::Apply(func, arg) => Apply(box translate_expr(*func), box translate_expr(*arg)),
            module::Literal(l) => Literal(Literal { typ: typ, value: l }),
            module::Lambda(arg, body) => {
                match arg {
                    IdentifierPattern(arg) => Lambda(Id::new(arg, typ, ~[]), box translate_expr_rest(*body)),
                    WildCardPattern => Lambda(Id::new(Name { name: intern("_"), uid: -1 }, typ, ~[]), box translate_expr_rest(*body)),
                    _ => fail!("Core translation of pattern matches in lambdas are not implemented")
                }
            }
            module::Let(bindings, body) => {
                let bs = translate_bindings(bindings);
                Let(bs, box translate_expr(*body))
            }
            module::Case(expr, alts) => {
                let a = FromVec::<Alternative<Id<Name>>>::from_vec(alts.move_iter().map(|alt| {
                    let module::Alternative { pattern: pattern, expression: expr} = alt;
                    let p = translate_pattern(pattern.node);
                    Alternative { pattern: p, expression:translate_expr(expr) }
                }).collect());
                Case(box translate_expr(*expr), a)
            }
            module::Do(bindings, expr) => {
                let mut result = translate_expr(*expr);
                for bind in bindings.move_iter().rev() {
                    result = match bind {
                        module::DoExpr(e) => {
                            let core = translate_expr(e);
                            let x = do_bind2_id(core.get_type().clone(), result.get_type().clone());
                            Apply(box Apply(box x, box core), box result)
                        }
                        module::DoBind(pattern, e) => {
                            do_bind_translate(pattern.node, translate_expr(e), result)
                        }
                        module::DoLet(bs) => {
                            Let(translate_bindings(bs), box result)
                        }
                    };
                }
                result
            }
        }
    }

    fn do_bind2_id(m_a: Type, m_b: Type) -> Expr<Id<Name>> {
        debug!("m_a {}", m_a);
        let c = match *m_a.appl() {
            TypeVariable(ref var) => ~[Constraint { class: intern("Monad"), variables: ~[var.clone()] }],
            _ => ~[]
        };
        let typ = function_type_(m_a, function_type_(m_b.clone(), m_b));
        Identifier(Id::new(Name { name: intern(">>"), uid: 0}, typ, c))
    }
    fn do_bind_translate(pattern: Pattern<Name>, expr: Expr<Id<Name>>, result: Expr<Id<Name>>) -> Expr<Id<Name>> {
        //do {p <- e; stmts} 	=
        //    let ok p = do {stmts}
		//        ok _ = fail "..."
		//    in e >>= ok
        let m_a = expr.get_type().clone();
        let a = m_a.appr().clone();
        let m_b = result.get_type().clone();
                debug!("m_a {}", m_a);
        let c = match *m_a.appl() {
            TypeVariable(ref var) => ~[Constraint { class: intern("Monad"), variables: ~[var.clone()] }],
            _ => ~[]
        };
        let arg2_type = function_type_(a.clone(), m_b.clone());
        let bind_typ = function_type_(m_a, function_type_(arg2_type.clone(), m_b.clone()));
        let bind_ident = Identifier(Id::new(Name { name: intern(">>="), uid: 0}, bind_typ, c.clone()));

        //Create ok binding
        let func_ident = Id::new(
            Name { name: intern("#ok"), uid: 0 },
            arg2_type.clone(),
            c.clone()
        );//TODO unique id
        let var = Id::new(Name { name: intern("p"), uid: 0 }, function_type_(a, m_b.clone()), c.clone());//Constraints for a
        let fail_ident = Identifier(Id::new(Name { name: intern("fail"), uid: 0 }, function_type_(list_type(char_type()), m_b), c));
        let func = Lambda(var.clone(), box Case(box Identifier(var), 
            ~[Alternative { pattern: translate_pattern(pattern), expression: result }
            , Alternative { pattern: WildCardPattern, expression: Apply(box fail_ident, box string("Unmatched pattern in let")) } ]));
        let bind = Binding { name: func_ident.clone(), expression: func };
        
        Let(~[bind], box mkApply(bind_ident, ~[expr, Identifier(func_ident)]))
    }

    fn translate_bindings(bindings: ~[module::Binding<Name>]) -> ~[Binding<Id<Name>>] {
        let mut result = Vec::new();
        let mut vec: Vec<module::Binding<Name>> = Vec::new();
        for bind in bindings.move_iter() {
            if vec.len() > 0 && vec.get(0).name != bind.name {
                result.push(translate_binding_group(vec));
                vec = Vec::new();
            }
            vec.push(bind);
        }
        if vec.len() > 0 {
            result.push(translate_binding_group(vec));
        }
        FromVec::from_vec(result)
    }
    fn translate_binding_group(mut bindings: Vec<module::Binding<Name>>) -> Binding<Id<Name>> {
        let mut name = Name { name: intern(""), uid: -1 };
        let mut context = ~[];
        let expr = if bindings.get(0).arguments.len() == 0 {
            let module::Binding {
                name: bind_name, arguments: _arguments,
                matches: matches, typeDecl: type_decl, ..
            } = bindings.pop().unwrap();
            name = bind_name;
            context = type_decl.context;
            translate_match(matches)
        }
        else if bindings.len() == 1 && simple_binding(bindings.get(0)) {
            let module::Binding {
                name: bind_name, arguments: arguments,
                matches: matches, typeDecl: type_decl, ..
            } = bindings.pop().unwrap();
            name = bind_name;
            context = type_decl.context.clone();
            let mut typ = &type_decl.typ;
            let arg_names = arguments.move_iter().map(|pattern| {
                let mut p = match translate_pattern(pattern) {
                    IdentifierPattern(name) => name,
                    WildCardPattern => Id::new(Name { name: intern("_"), uid: -1 }, Type::new_var(99999), ~[]),
                    _ => fail!()
                };
                p.typ = typ.clone();
                typ = match *typ {
                    TypeApplication(_, ref next) => &**next,
                    _ => typ//We dont actually have a function type which we need, so we are likely in a unittest
                            //just reuse the same type so we do not crash
                };
                p
            });
            make_lambda(arg_names, translate_match(matches))
        }
        else {
            let arg_len = bindings.get(0).arguments.len();
            let match_expr : Expr<Id<Name>> = {
                let (name, tuple_typ) = module::tuple_type(arg_len);
                let id = Id::new(Name { name: intern(name.as_slice()), uid: 0 }, tuple_typ, ~[]);
                Identifier(id.clone())
            };
            let args: Vec<Id<Name>> = {
                let mut typ = &bindings.get(0).typeDecl.typ;
                make_arguments(range(0, bindings.get(0).arguments.len()).map(|_| {
                    let f = typ;
                    typ = match *typ {
                        TypeApplication(_, ref next) => &**next,
                        _ => typ
                    };
                    f
                })).collect()
            };
            let match_expr = {
                let mut args = make_arguments(arg_iterator(&bindings.get(0).typeDecl.typ)).map(|id| Identifier(id));
                if bindings.get(0).arguments.len() == 1 {//Avoid tuple single argument functions
                    args.next().unwrap()
                }
                else {
                    apply(match_expr, args)
                }
            };
            let alts: Vec<Alternative<Id<Name>>> = bindings.move_iter().map(|bind| {
                let module::Binding { name: bind_name, arguments: arguments, matches: matches, typeDecl: type_decl, .. } = bind;
                name = bind_name;
                context = type_decl.context;
                make_alternative(arguments, translate_match(matches))
            }).collect();
            make_lambda(args.move_iter(), Case(box match_expr, FromVec::from_vec(alts)))
        };
        Binding {
            name: Id::new(name, expr.get_type().clone(), context),
            expression: expr
        }
    }
    
    struct ArgIterator<'a> {
        typ: &'a Type
    }
    impl <'a> Iterator<&'a Type> for ArgIterator<'a> {
        fn next(&mut self) -> Option<&'a Type> {
            match *self.typ {
                TypeApplication(ref lhs, ref rhs) => {
                    match **lhs {
                        TypeApplication(ref func, ref arg) => {
                            match **func {
                                TypeOperator(ref op) if op.name.as_slice() == "->" => {
                                    self.typ = &**rhs;
                                    Some(&**arg)
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
    }
    fn arg_iterator<'a>(typ: &'a Type) -> ArgIterator<'a> {
        ArgIterator { typ: typ }
    }

    fn make_arguments<'a, 'b, I : Iterator<&'b Type>>(iter: I) -> ::std::iter::Map<'a, (uint, &'b Type), Id<Name>, ::std::iter::Enumerate<I>> {
        iter.enumerate().map(|(index, typ)| {
            let arg_name = Name { name: intern(index.to_str().as_slice()), uid: -100 };
            Id::new(arg_name, typ.clone(), ~[])
        })
    }

    fn simple_binding(binding: &module::Binding<Name>) -> bool {
        binding.arguments.iter().all(|arg| {
            match *arg {
                WildCardPattern | IdentifierPattern(..) => true,
                _ => false
            }
        })
    }

    fn apply<T, I: Iterator<Expr<T>>>(mut func: Expr<T>, mut iter: I) -> Expr<T> {
        for arg in iter {
            func = Apply(box func, box arg);
        }
        func
    }

    fn make_lambda<T, I: Iterator<T>>(mut iter: I, body: Expr<T>) -> Expr<T> {
        match iter.next() {
            Some(arg) => Lambda(arg, box make_lambda(iter, body)),
            None => body
        }
    }
    

    fn make_alternative(arguments: ~[Pattern<Name>], body: Expr<Id<Name>>) -> Alternative<Id<Name>> {
        if arguments.len() == 1 {
            Alternative { pattern: translate_pattern(arguments[0]), expression: body }
        }
        else {
            let (tuple_name, tuple_typ) = module::tuple_type(arguments.len());
            let tuple_id = Id::new(Name { name: intern(tuple_name.as_slice()), uid: 0 }, tuple_typ, ~[]);
            let patterns: Vec<Pattern<Id<Name>>> = arguments.move_iter().map(|arg| translate_pattern(arg)).collect();
            Alternative { pattern: ConstructorPattern(tuple_id, FromVec::from_vec(patterns)), expression: body }
        }
    }

    fn translate_pattern(pattern: module::Pattern<Name>) -> Pattern<Id<Name>> {
        match pattern {
            IdentifierPattern(i) => IdentifierPattern(Id::new(i, Type::new_var(1213), ~[])),
            NumberPattern(n) => NumberPattern(n),
            ConstructorPattern(name, patterns) =>
                ConstructorPattern(
                    Id::new(name, Type::new_var(444), ~[]),
                    FromVec::<Pattern<Id<Name>>>::from_vec(patterns.move_iter().map(translate_pattern).collect())),
            WildCardPattern => WildCardPattern
        }
    }

    fn string(s: &str) -> Expr<Id<Name>> {
        Literal(Literal { typ: list_type(char_type()), value: String(intern(s)) })
    }
    fn mkApply(func: Expr<Id<Name>>, args: ~[Expr<Id<Name>>]) -> Expr<Id<Name>> {
        let mut result = func;
        for arg in args.move_iter() {
            result = Apply(box result, box arg);
        }
        result
    }
}
