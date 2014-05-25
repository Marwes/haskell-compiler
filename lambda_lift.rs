use collections::hashmap::HashMap;
use std::vec::FromVec;
use core::*;
use module::function_type_;
use interner::*;

pub type TypeAndStr = Id;

pub fn do_lambda_lift(module: Module<TypeAndStr>) -> Module<Id> {
    lift_lambdas(abstract_module(module))
}

struct FreeVariables {
    uid: uint
}

fn each_pattern_variables(pattern: &Pattern<Id>, f: &mut |&Name|) {
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
            let f = box self.free_variables(variables, free_vars, *func);
            let a = box self.free_variables(variables, free_vars, *arg);
            Apply(f, a)
        }
        Lambda(arg, body) => {
            variables.insert_or_update_with(arg.name.clone(), 1, |_, v| *v += 1);
            let b = self.free_variables(variables, free_vars, *body);
            *variables.get_mut(&arg.name) -= 1;
            free_vars.remove(&arg.name);//arg was not actually a free variable
            Lambda(arg, box b)
        }
        Let(mut bindings, expr) => {
            for bind in bindings.iter() {
                variables.insert_or_update_with(bind.name.name.clone(), 1, |_, v| *v += 1);
            }
            let mut free_vars2 = HashMap::new();
            for bind in bindings.mut_iter() {
                free_vars2.clear();
                update(&mut bind.expression, |bind_expr| self.free_variables(variables, &mut free_vars2, bind_expr));
                //free_vars2 is the free variables for this binding
                for (k, v) in free_vars2.iter() {
                    free_vars.insert(k.clone(), v.clone());
                }
                update(&mut bind.expression, |e| self.abstract(&free_vars2, e));
            }
            let e = box self.free_variables(variables, free_vars, *expr);
            for bind in bindings.iter() {
                *variables.get_mut(&bind.name.name) -= 1;
                free_vars.remove(&bind.name.name);
            }
            Let(bindings, e)
        }
        Case(expr, mut alts) => {
            let e = self.free_variables(variables, free_vars, *expr);
            for alt in alts.mut_iter() {
                each_pattern_variables(&alt.pattern, &mut |name| {
                    variables.insert_or_update_with(name.clone(), 1, |_, v| *v += 1);
                });
                update(&mut alt.expression, |expression| self.free_variables(variables, free_vars, expression));
                each_pattern_variables(&alt.pattern, &mut |name| {
                    *variables.get_mut(name) -= 1;
                    free_vars.remove(name);//arg was not actually a free variable
                });
            }
            Case(box e, alts)
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
                rhs = Lambda(var.clone(), box rhs);
                typ = function_type_(var.get_type().clone(), typ);
            }
            self.uid += 1;
            let bind = Binding {
                name: Id::new(Name {name: intern("#sc"), uid: self.uid }, typ.clone(), box []),
                expression: rhs
            };
            Let(~[bind], box Identifier(Id::new(Name { name: intern("#sc"), uid: self.uid }, typ.clone(), ~[])))
        };
        for (_, var) in free_vars.iter() {
            e = Apply(box e, box Identifier(var.clone()));
        }
        e
    }
}
}

fn lift_lambdas_expr<T>(expr: Expr<T>, out_lambdas: &mut Vec<Binding<T>>) -> Expr<T> {
    match expr {
        Apply(func, arg) => Apply(box lift_lambdas_expr(*func, out_lambdas), box lift_lambdas_expr(*arg, out_lambdas)),
        Lambda(arg, body) => Lambda(arg, box lift_lambdas_expr(*body, out_lambdas)),
        Let(bindings, expr) => {
            let mut new_binds = Vec::new();
            for mut bind in bindings.move_iter() {
                let is_lambda = match bind.expression {
                    Lambda(..) => true,
                    _ => false
                };
                update(&mut bind.expression, |expression| lift_lambdas_expr(expression, out_lambdas));
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
                Let(FromVec::from_vec(new_binds), box lift_lambdas_expr(*expr, out_lambdas))
            }
        }
        Case(expr, mut alts) => {
            for alt in alts.mut_iter() {
                update(&mut alt.expression, |expression| lift_lambdas_expr(expression, out_lambdas));
            }
            Case(box lift_lambdas_expr(*expr, out_lambdas), alts)
        }
        _ => expr
    }
}
pub fn lift_lambdas<T: ::std::fmt::Show>(mut module: Module<T>) -> Module<T> {
    update(&mut module.bindings, |bindings| {
        let mut new_bindings : Vec<Binding<T>> = Vec::new();
        let mut bindings2 : Vec<Binding<T>> = bindings.move_iter()
            .map(|mut bind| {
                update(&mut bind.expression, |expression| lift_lambdas_expr(expression, &mut new_bindings));
                bind
            }).collect();
        bindings2.extend(new_bindings.move_iter());
        FromVec::from_vec(bindings2)
    });
    module
}

fn update<T>(x: &mut T, f: |T| -> T) {
    use std::mem::{swap, forget, uninit};
    let mut temp = unsafe { uninit() };
    swap(x, &mut temp);
    temp = f(temp);
    swap(x, &mut temp);
    unsafe { forget(temp) };
}

pub fn abstract_module(module: Module<TypeAndStr>) -> Module<TypeAndStr> {
    use core::result::*;
    impl Visitor<TypeAndStr> for FreeVariables {
        fn visit_binding(&mut self, bind: Binding<TypeAndStr>) -> Binding<TypeAndStr> {
            let Binding { name: name, expression: bind_expr } = bind;
            let mut variables = HashMap::new();
            let mut free_vars = HashMap::new();
            let e = self.free_variables(&mut variables, &mut free_vars, bind_expr);
            Binding { name: name, expression: e }
        }
    }
    let mut this = FreeVariables { uid: 1 };
    this.visit_module(module)
}

#[cfg(test)]
mod tests {
    use test::Bencher;
    use interner::*;
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

    fn check_args(expr: &Expr<Id>, args: &[InternedStr]) -> bool {
        match expr {
            &Lambda(ref arg, ref body) => arg.name.name == args[0] && check_args(*body, args.slice_from(1)),
            _ => args.len() == 0
        }
    }

    struct CheckAbstract {
        count: int
    }
    
    fn get_let<'a>(expr: &'a Expr<Id>, args: &mut Vec<InternedStr>) -> &'a Expr<Id> {
        match expr {
            &Apply(ref f, ref arg) => {
                let a: &Expr<Id> = *arg;
                match a {
                    &Identifier(ref i) => args.push(i.name.name),
                    _ => fail!("Expected identifier as argument")
                }
                get_let(*f, args)
            }
            _ => expr
        }
    }

    impl Visitor<Id> for CheckAbstract {
        fn visit_binding(&mut self, bind: &Binding<Id>) {
            if intern("f") == bind.name.name.name {
                let mut args = Vec::new();
                match get_let(&bind.expression, &mut args) {
                    &Let(ref binds, ref body) => {
                        //Push the argument of the function itself
                        args.push(intern("x"));
                        assert!(check_args(&binds[0].expression, args.as_slice()));
                        assert_eq!(Identifier(binds[0].name.clone()), **body);
                    }
                    _ => assert!(false, "Expected Let, found {}", bind.expression)
                }
                self.count += 1;
            }
            else if intern("g") == bind.name.name.name {
                let mut args = Vec::new();
                match get_let(&bind.expression, &mut args) {
                    &Let(ref binds, ref body) => {
                        args.push(intern("y"));
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

    #[bench]
    fn bench(b: &mut Bencher) {
        use std::io::File;
        use typecheck::do_typecheck;

        let path = &Path::new("Prelude.hs");
        let contents = File::open(path).read_to_str().unwrap();
        let module = do_typecheck(contents.as_slice());
        b.iter(|| {
            do_lambda_lift(translate_module(module.clone()))
        });
    }
}
