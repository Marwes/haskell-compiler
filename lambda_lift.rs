use collections::hashmap::HashMap;
use core::*;
use scoped_map::ScopedMap;
use typecheck::function_type_;

pub type TypeAndStr = (~[Constraint], Type, ~str);

pub fn do_lambda_lift(module: Module<TypeAndStr>) -> Module<Id> {
    lift_lambdas(rename_module(abstract_module(module)))
}

//Walks through an expression and notes all the free variables and for each lambda, adds the
//free variables to its arguments and performs an immediate application
//@variables All the local variables in scope, values are how many of the name there exists
//@free_vars The free variables for the returned expression
fn free_variables(variables: &mut HashMap<~str, int>, free_vars: &mut HashMap<~str, TypeAndStr>, expr: Expr<TypeAndStr>) -> Expr<TypeAndStr> {
    match expr {
        Identifier(i) => {
            //If the identifier is a local, add it to the free variables
            if variables.find(i.ref2()).map(|x| *x > 0).unwrap_or(false) {
                free_vars.insert(i.ref2().clone(), i.clone());
            }
            Identifier(i)
        }
        Apply(func, arg) => {
            let f = ~free_variables(variables, free_vars, *func);
            let a = ~free_variables(variables, free_vars, *arg);
            Apply(f, a)
        }
        Lambda(arg, body) => {
            variables.insert_or_update_with(arg.ref2().clone(), 1, |_, v| *v += 1);
            let b = free_variables(variables, free_vars, *body);
            *variables.get_mut(arg.ref2()) -= 1;
            free_vars.remove(arg.ref2());//arg was not actually a free variable
            Lambda(arg, ~b)
        }
        Let(bindings, expr) => {
            for bind in bindings.iter() {
                variables.insert_or_update_with(bind.name.ref2().clone(), 1, |_, v| *v += 1);
            }
            let mut free_vars2 = HashMap::new();
            let new_bindings: ~[Binding<TypeAndStr>] = bindings.move_iter().map(
                |Binding { name: name, expression: bind_expr }| {
                free_vars2.clear();
                let e = free_variables(variables, &mut free_vars2, bind_expr);
                //free_vars2 is the free variables for this binding
                for (k, v) in free_vars2.iter() {
                    free_vars.insert(k.clone(), v.clone());
                }
                Binding{
                    name: name,
                    expression: abstract(&free_vars2, e)
                }
            }).collect();
            let e = ~free_variables(variables, free_vars, *expr);
            for bind in new_bindings.iter() {
                *variables.get_mut(bind.name.ref2()) -= 1;
                free_vars.remove(bind.name.ref2());
            }
            Let(new_bindings, e)
        }
        Case(expr, alts) => {
            Case(expr, alts)
        }
        e => e
    }
}

fn abstract(free_vars: &HashMap<~str, TypeAndStr>, input_expr: Expr<TypeAndStr>) -> Expr<TypeAndStr> {
    if free_vars.len() == 0 {
        input_expr
    }
    else {
        let mut e = {
            let mut rhs = input_expr;
            let mut typ = rhs.get_type().clone();
            for (_, var) in free_vars.iter() {
                rhs = Lambda(var.clone(), ~rhs);
                typ = function_type_(var.ref1().clone(), typ);
            }
            let bind = Binding {
                name: (~[], typ.clone(), "sc".to_owned()),
                expression: rhs
            };
            Let(~[bind], ~Identifier((~[], typ.clone(), "sc".to_owned())))
        };
        for (_, var) in free_vars.iter() {
            e = Apply(~e, ~Identifier(var.clone()));
        }
        e
    }
}

struct Renamer {
    uniques: ScopedMap<~str, Name>,
    unique_id: uint
}
impl Renamer {

    fn rename_bindings(&mut self, bindings: ~[Binding<TypeAndStr>]) -> ~[Binding<Id>] {
        //Add all bindings in the scope
        for bind in bindings.iter() {
            self.make_unique(bind.name.ref2().clone());
        }
        bindings.move_iter().map(|binding| {
            let Binding { name: (constraints, typ, name), expression: expression } = binding;
            let n = self.uniques.find(&name).map(|u| u.clone())
                .expect(format!("Error: lambda_lift: Undefined variable {}", name));
            Binding {
                name: Id::new(n, typ, constraints),
                expression: self.rename(expression)
            }
        }).collect()
    }

    fn rename(&mut self, expr: Expr<TypeAndStr>) -> Expr<Id> {
        match expr {
            Literal(l) => Literal(l),
            Identifier((constraints, typ, i)) => {
                let n = match self.uniques.find(&i).map(|u| u.clone()) {
                    Some(n) => n,
                    None => Name { name: i, uid: 0 }//If the variable is not found in variables it is a global variable
                };
                Identifier(Id::new(n, typ, constraints))
            }
            Apply(func, arg) => Apply(~self.rename(*func), ~self.rename(*arg)),
            Lambda((constraints, typ, arg), body) => {
                self.uniques.enter_scope();
                let l = Lambda(Id::new(self.make_unique(arg), typ, constraints), ~self.rename(*body));
                self.uniques.exit_scope();
                l
            }
            Let(bindings, expr) => {
                self.uniques.enter_scope();
                let bs = self.rename_bindings(bindings);
                let l = Let(bs, ~self.rename(*expr));
                self.uniques.exit_scope();
                l
            }
            Case(expr, alts) => {
                let a = alts.move_iter().map(|Alternative { pattern: pattern, expression: expression }| {
                    self.uniques.enter_scope();
                    let a = Alternative {
                        pattern: self.rename_pattern(pattern),
                        expression: self.rename(expression)
                    };
                    self.uniques.exit_scope();
                    a
                }).collect();
                Case(~self.rename(*expr), a)
            }
        }
    }

    fn rename_pattern(&mut self, pattern: Pattern<TypeAndStr>) -> Pattern<Id> {
        match pattern {
            NumberPattern(i) => NumberPattern(i),
            ConstructorPattern(s, ps) => {
                let ps2 = ps.move_iter().map(|p| self.rename_pattern(p)).collect();
                ConstructorPattern(s, ps2)
            }
            IdentifierPattern((constraints, typ, s)) => IdentifierPattern(Id::new(self.make_unique(s), typ, constraints))
        }
    }

    fn make_unique(&mut self, name: ~str) -> Name {
        self.unique_id += 1;
        let u = Name { name: name.clone(), uid: self.unique_id};
        self.uniques.insert(name, u.clone());
        u
    }
}

fn lift_lambdas_expr<T>(expr: Expr<T>, out_lambdas: &mut Vec<Binding<T>>) -> Expr<T> {
    match expr {
        Apply(func, arg) => Apply(~lift_lambdas_expr(*func, out_lambdas), ~lift_lambdas_expr(*arg, out_lambdas)),
        Lambda(arg, body) => Lambda(arg, ~lift_lambdas_expr(*body, out_lambdas)),
        Let(bindings, expr) => {
            let mut new_binds = Vec::new();
            for Binding { name: name, expression: expression } in bindings.move_iter() {
                let is_lambda = match &expression {
                    &Lambda(..) => true,
                    _ => false
                };
                let bind = Binding { name: name, expression: lift_lambdas_expr(expression, out_lambdas) };
                if is_lambda {
                    out_lambdas.push(bind);
                }
                else {
                    new_binds.push(bind);
                }
            }
            if new_binds.len() == 0 {
                lift_lambdas_expr(*expr, out_lambdas)
            }
            else {
                Let(new_binds.move_iter().collect(), ~lift_lambdas_expr(*expr, out_lambdas))
            }
        }
        Case(expr, alts) => {
            let a = alts.move_iter().map(|Alternative { pattern: pattern, expression: expression }| {
                Alternative { pattern: pattern, expression: lift_lambdas_expr(expression, out_lambdas) }
            }).collect();
            Case(~lift_lambdas_expr(*expr, out_lambdas), a)
        }
        _ => expr
    }
}
pub fn lift_lambdas<T: ::std::fmt::Show>(module: Module<T>) -> Module<T> {
    let Module {
        classes : classes,
        data_definitions: data_definitions,
        bindings : bindings,
        instances: instances
    } = module;
    
    let mut new_bindings : Vec<Binding<T>> = Vec::new();
    let bindings2 : ~[Binding<T>] = bindings.move_iter().map(|Binding { name: name, expression: expression }| {
        Binding { name: name, expression: lift_lambdas_expr(expression, &mut new_bindings) }
    }).collect();

    Module {
        classes : classes,
        data_definitions: data_definitions,
        bindings : bindings2.move_iter().chain(new_bindings.move_iter()).collect(),
        instances: instances
    }
}


pub fn rename_module(module: Module<TypeAndStr>) -> Module<Id> {
    let mut renamer = Renamer { uniques: ScopedMap::new(), unique_id: 1 };
    let Module {
        classes : classes,
        data_definitions: data_definitions,
        bindings : bindings,
        instances: instances
    } = module;
    
    let bindings2 = bindings.move_iter().map(|binding| {
        let Binding { name: (constraints, typ, name), expression: expression } = binding;
        Binding {
            name: Id::new(Name { name: name, uid: 0 }, typ, constraints),
            expression: renamer.rename(expression)
        }
    }).collect();
    
    Module {
        classes : classes,
        data_definitions: data_definitions,
        bindings : bindings2,
        instances: instances
    }
}
pub fn abstract_module(module: Module<TypeAndStr>) -> Module<TypeAndStr> {
    each_binding(module,
        |name| name,
        |bind| {
            let Binding { name: name, expression: bind_expr } = bind;
            let mut variables = HashMap::new();
            let mut free_vars = HashMap::new();
            let e = free_variables(&mut variables, &mut free_vars, bind_expr);
            Binding { name: name, expression: e }
        })
}

pub fn each_binding<Ident, Ident2>(module: Module<Ident>, _trans: |Ident| -> Ident2, bind_f: |Binding<Ident>| -> Binding<Ident2>) -> Module<Ident2> {
    let Module {
        classes : classes,
        data_definitions: data_definitions,
        bindings : bindings,
        instances: instances
    } = module;
    
    let bindings2 = bindings.move_iter().map(|x| bind_f(x)).collect();
    
    Module {
        classes : classes,
        data_definitions: data_definitions,
        bindings : bindings2,
        instances: instances
    }
}


#[cfg(test)]
mod tests {
    use lambda_lift::*;
    use collections::hashmap::HashSet;
    use parser::Parser;
    use core::*;
    use core::translate::translate_module;

    struct CheckUniques {
        found: HashSet<Id>
    }

    impl Visitor<Id> for CheckUniques {
        fn visit_binding(&mut self, bind: &Binding<Id>) {
            assert!(self.found.insert(bind.name.clone()));
            self.visit_expr(&bind.expression);
        }
        fn visit_expr(&mut self, expr: &Expr<Id>) {
            match expr {
                &Lambda(ref i, _) => {
                    assert!(self.found.insert(i.clone()));
                }
                _ => ()
            }
            walk_expr(self, expr)
        }
    }

    #[test]
    fn all_uniques() {
        let mut visitor = CheckUniques { found: HashSet::new() };
        let mut parser = Parser::new(
r"add x y = 2
test = 3.14
test2 x =
    let
        test = 2
        f x =
            let g y = add x (f y)
            in add x test
    in f x".chars());
        let m = translate_module(parser.module());
        let module = rename_module(m);
        (&mut visitor as &mut Visitor<Id>).visit_module(&module);
    }

    fn check_args(expr: &Expr<Id>, args: &[&str]) -> bool {
        match expr {
            &Lambda(ref arg, ref body) => arg.name.name.equiv(&args[0]) && check_args(*body, args.slice_from(1)),
            _ => args.len() == 0
        }
    }

    struct CheckAbstract {
        count: int
    }
    
    fn get_let<'a>(expr: &'a Expr<Id>, args: &mut Vec<&'a str>) -> &'a Expr<Id> {
        match expr {
            &Apply(ref f, ref arg) => {
                let a: &Expr<Id> = *arg;
                match a {
                    &Identifier(ref i) => args.push(i.name.name.as_slice()),
                    _ => fail!("Expected identifier as argument")
                }
                get_let(*f, args)
            }
            _ => expr
        }
    }

    impl Visitor<Id> for CheckAbstract {
        fn visit_binding(&mut self, bind: &Binding<Id>) {
            if "f" == bind.name.name.name {
                let mut args = Vec::new();
                match get_let(&bind.expression, &mut args) {
                    &Let(ref binds, ref body) => {
                        //Push the argument of the function itself
                        args.push("x");
                        assert!(check_args(&binds[0].expression, args.as_slice()));
                        assert_eq!(Identifier(binds[0].name.clone()), **body);
                    }
                    _ => assert!(false, "Expected Let, found {}", bind.expression)
                }
                self.count += 1;
            }
            else if "g" == bind.name.name.name {
                let mut args = Vec::new();
                match get_let(&bind.expression, &mut args) {
                    &Let(ref binds, ref body) => {
                        args.push("y");
                        assert!(check_args(&binds[0].expression, args.as_slice()));
                        assert_eq!(Identifier(binds[0].name.clone()), **body);
                    }
                    _ => assert!(false, "Expected Let")
                }
                self.count += 1;
            }
            self.visit_expr(&bind.expression);
        }
    }

    #[test]
    fn all_free_vars() {
        let mut visitor = CheckAbstract { count: 0 };
        let mut parser = Parser::new(
r"add x y = 2
test = 3.14
test2 x =
    let
        test = 2
        f x =
            let g y = add x (f y)
            in add x test
    in f x".chars());
        let m = translate_module(parser.module());
        let module = rename_module(abstract_module(m));
        (&mut visitor as &mut Visitor<Id>).visit_module(&module);
        assert_eq!(visitor.count, 2);
    }

    struct NoLambdas;

    impl <T> Visitor<T> for NoLambdas {
        fn visit_expr(&mut self, expr: &Expr<T>) {
            match expr {
                &Lambda(..) => assert!(false, "Found lambda in expression"),
                _ => ()
            }
            walk_expr(self, expr);
        }
    }
    #[test]
    fn no_local_lambdas() {
        fn skip_lambdas<'a, T>(expr: &'a Expr<T>) -> &'a Expr<T> {
            match expr {
                &Lambda(_, ref body) => skip_lambdas(*body),
                _ => expr
            }
        }

        let mut visitor = NoLambdas;
        let mut parser = Parser::new(
r"add x y = 2
test = 3.14
test2 x =
    let
        test = 2
        f x =
            let g y = add x (f y)
            in add x test
    in f x".chars());
        let m = translate_module(parser.module());
        let module = lift_lambdas(m);
        for bind in module.bindings.iter() {
            (&mut visitor as &mut Visitor<TypeAndStr>).visit_expr(skip_lambdas(&bind.expression));
        }
    }
}
