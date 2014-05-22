use collections::hashmap::HashMap;
use core::*;
use module::function_type_;

pub type TypeAndStr = Id;

pub fn do_lambda_lift(module: Module<TypeAndStr>) -> Module<Id> {
    lift_lambdas(abstract_module(module))
}

struct FreeVariables {
    uid: uint
}

fn each_pattern_variables(pattern: &Pattern<Id>, f: &|&Name|) {
    match *pattern {
        IdentifierPattern(ref ident) => (*f)(&ident.name),
        ConstructorPattern(_, ref patterns) => {
            for p in patterns.iter() {
                each_pattern_variables(p, f);
            }
        }
        _ => ()
    }
}


impl FreeVariables {

//Walks through an expression and notes all the free variables and for each lambda, adds the
//free variables to its arguments and performs an immediate application
//@variables All the local variables in scope, values are how many of the name there exists
//@free_vars The free variables for the returned expression
fn free_variables(&mut self, variables: &mut HashMap<Name, int>, free_vars: &mut HashMap<Name, TypeAndStr>, expr: Expr<TypeAndStr>) -> Expr<TypeAndStr> {
    match expr {
        Identifier(i) => {
            //If the identifier is a local, add it to the free variables
            if variables.find(&i.name).map(|x| *x > 0).unwrap_or(false) {
                free_vars.insert(i.name.clone(), i.clone());
            }
            Identifier(i)
        }
        Apply(func, arg) => {
            let f = ~self.free_variables(variables, free_vars, *func);
            let a = ~self.free_variables(variables, free_vars, *arg);
            Apply(f, a)
        }
        Lambda(arg, body) => {
            variables.insert_or_update_with(arg.name.clone(), 1, |_, v| *v += 1);
            let b = self.free_variables(variables, free_vars, *body);
            *variables.get_mut(&arg.name) -= 1;
            free_vars.remove(&arg.name);//arg was not actually a free variable
            Lambda(arg, ~b)
        }
        Let(bindings, expr) => {
            for bind in bindings.iter() {
                variables.insert_or_update_with(bind.name.name.clone(), 1, |_, v| *v += 1);
            }
            let mut free_vars2 = HashMap::new();
            let new_bindings: ~[Binding<TypeAndStr>] = bindings.move_iter().map(
                |Binding { name: name, expression: bind_expr }| {
                free_vars2.clear();
                let e = self.free_variables(variables, &mut free_vars2, bind_expr);
                //free_vars2 is the free variables for this binding
                for (k, v) in free_vars2.iter() {
                    free_vars.insert(k.clone(), v.clone());
                }
                Binding{
                    name: name,
                    expression: self.abstract(&free_vars2, e)
                }
            }).collect();
            let e = ~self.free_variables(variables, free_vars, *expr);
            for bind in new_bindings.iter() {
                *variables.get_mut(&bind.name.name) -= 1;
                free_vars.remove(&bind.name.name);
            }
            Let(new_bindings, e)
        }
        Case(expr, alts) => {
            let e = self.free_variables(variables, free_vars, *expr);
            let a = alts.move_iter().map(|Alternative { pattern: pattern, expression: expression }| {
                each_pattern_variables(&pattern, &|name| {
                    variables.insert_or_update_with(name.clone(), 1, |_, v| *v += 1);
                });
                let e = self.free_variables(variables, free_vars, expression);
                each_pattern_variables(&pattern, &|name| {
                    *variables.get_mut(name) -= 1;
                    free_vars.remove(name);//arg was not actually a free variable
                });
                Alternative { pattern: pattern, expression: e }
            }).collect();
            Case(~e, a)
        }
        e => e
    }
}

fn abstract(&mut self, free_vars: &HashMap<Name, TypeAndStr>, input_expr: Expr<TypeAndStr>) -> Expr<TypeAndStr> {
    if free_vars.len() == 0 {
        input_expr
    }
    else {
        let mut e = {
            let mut rhs = input_expr;
            let mut typ = rhs.get_type().clone();
            for (_, var) in free_vars.iter() {
                rhs = Lambda(var.clone(), ~rhs);
                typ = function_type_(var.get_type().clone(), typ);
            }
            self.uid += 1;
            let bind = Binding {
                name: Id::new(Name {name: "#sc".to_owned(), uid: self.uid }, typ.clone(), ~[]),
                expression: rhs
            };
            Let(~[bind], ~Identifier(Id::new(Name { name: "#sc".to_owned(), uid: self.uid }, typ.clone(), ~[])))
        };
        for (_, var) in free_vars.iter() {
            e = Apply(~e, ~Identifier(var.clone()));
        }
        e
    }
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

pub fn abstract_module(module: Module<TypeAndStr>) -> Module<TypeAndStr> {
    let mut this = FreeVariables { uid: 1 };
    each_binding(module,
        |name| name,
        |bind| {
            let Binding { name: name, expression: bind_expr } = bind;
            let mut variables = HashMap::new();
            let mut free_vars = HashMap::new();
            let e = this.free_variables(&mut variables, &mut free_vars, bind_expr);
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
    use renamer::rename_module;

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
        let module = translate_module(rename_module(parser.module()));
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
        let m = translate_module(rename_module(parser.module()));
        let module = abstract_module(m);
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
        let m = translate_module(rename_module(parser.module()));
        let module = lift_lambdas(m);
        for bind in module.bindings.iter() {
            (&mut visitor as &mut Visitor<TypeAndStr>).visit_expr(skip_lambdas(&bind.expression));
        }
    }
}
