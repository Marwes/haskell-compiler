use collections::hashmap::{HashMap, HashSet};
use core::*;
use scoped_map::ScopedMap;

//Walks through an expression and notes all the free variables and for each lambda, adds the
//free variables to its arguments and performs an immediate application
//@variables All the local variables in scope, values are how many of the name there exists
//@free_vars The free variables for the returned expression
fn free_variables(variables: &mut HashMap<(Type, ~str), int>, free_vars: &mut HashSet<(Type, ~str)>, expr: Expr<(Type, ~str)>) -> Expr<(Type, ~str)> {
    match expr {
        Identifier(i) => {
            //If the identifier is a local, add it to the free variables
            if variables.find(&i).map(|x| *x > 0).unwrap_or(false) {
                free_vars.insert(i.clone());
            }
            Identifier(i)
        }
        Apply(func, arg) => {
            let f = ~free_variables(variables, free_vars, *func);
            let a = ~free_variables(variables, free_vars, *arg);
            Apply(f, a)
        }
        Lambda(arg, body) => {
            variables.insert_or_update_with(arg.clone(), 1, |_, v| *v += 1);
            let b = free_variables(variables, free_vars, *body);
            *variables.get_mut(&arg) -= 1;
            free_vars.remove(&arg);//arg was not actually a free variable
            Lambda(arg, ~b)
        }
        Let(bindings, expr) => {
            for bind in bindings.iter() {
                variables.insert_or_update_with(bind.name.clone(), 1, |_, v| *v += 1);
            }
            let mut free_vars2 = HashSet::new();
            let new_bindings: ~[Binding<(Type, ~str)>] = bindings.move_iter().map(
                |Binding { name: name, expression: bind_expr }| {
                free_vars2.clear();
                let e = free_variables(variables, &mut free_vars2, bind_expr);
                //free_vars2 is the free variables for this binding
                for v in free_vars2.iter() {
                    free_vars.insert(v.clone());
                }
                Binding{
                    name: name,
                    expression: abstract(&free_vars2, e)
                }
            }).collect();
            let e = ~free_variables(variables, free_vars, *expr);
            for bind in new_bindings.iter() {
                *variables.get_mut(&bind.name) -= 1;
                free_vars.remove(&bind.name);
            }
            Let(new_bindings, e)
        }
        Case(expr, alts) => {
            Case(expr, alts)
        }
        e => e
    }
}

fn abstract(free_vars: &HashSet<(Type, ~str)>, input_expr: Expr<(Type, ~str)>) -> Expr<(Type, ~str)> {
    let mut e = {
        let mut rhs = input_expr;
        for var in free_vars.iter() {
            rhs = Lambda(var.clone(), ~rhs);
        }
        let bind = Binding {
            name: (Type::new_var(0), "sc".to_owned()),
            expression: rhs
        };
        Let(~[bind], ~Identifier((Type::new_var(0), "sc".to_owned())))
    };
    for var in free_vars.iter() {
        e = Apply(~e, ~Identifier(var.clone()));
    }
    e
}

#[deriving(Eq, TotalEq, Hash, Clone, Show)]
pub struct Name {
    name: ~str,
    uid: uint
}
#[deriving(Eq, TotalEq, Hash, Clone, Show)]
pub struct Id {
    name: Name,
    typ: Type
}

struct Renamer {
    uniques: ScopedMap<~str, Name>,
    unique_id: uint
}
impl Renamer {

    fn rename_bindings(&mut self, bindings: ~[Binding<(Type, ~str)>]) -> ~[Binding<Id>] {
        //Add all bindings in the scope
        for bind in bindings.iter() {
            self.make_unique(bind.name.ref1().clone());
        }
        bindings.move_iter().map(|binding| {
            let Binding { name: (typ, name), expression: expression } = binding;
            let n = self.uniques.find(&name).map(|u| u.clone()).expect(format!("Undefined variable {}", name));
            Binding {
                name: Id { typ: typ, name: n },
                expression: self.rename(expression)
            }
        }).collect()
    }

    fn rename(&mut self, expr: Expr<(Type, ~str)>) -> Expr<Id> {
        match expr {
            Literal(l) => Literal(l),
            Identifier((typ, i)) => {
                let n = self.uniques.find(&i).map(|u| u.clone()).expect(format!("Undefined variable {}", i));
                Identifier(Id { typ: typ, name: n })
            }
            Apply(func, arg) => Apply(~self.rename(*func), ~self.rename(*arg)),
            Lambda((typ, arg), body) => {
                self.uniques.enter_scope();
                let l = Lambda(Id { typ: typ, name: self.make_unique(arg) }, ~self.rename(*body));
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

    fn rename_pattern(&mut self, pattern: Pattern<(Type, ~str)>) -> Pattern<Id> {
        match pattern {
            NumberPattern(i) => NumberPattern(i),
            ConstructorPattern(s, ps) => {
                let ps2 = ps.move_iter().map(|p| self.rename_pattern(p)).collect();
                ConstructorPattern(s, ps2)
            }
            IdentifierPattern((typ, s)) => IdentifierPattern(Id { typ: typ, name: self.make_unique(s) })
        }
    }

    fn make_unique(&mut self, name: ~str) -> Name {
        self.unique_id += 1;
        let u = Name { name: name.clone(), uid: self.unique_id};
        self.uniques.insert(name, u.clone());
        u
    }
}

pub fn rename_module(module: Module<(Type, ~str)>) -> Module<Id> {
    let mut renamer = Renamer { uniques: ScopedMap::new(), unique_id: 0 };
    let Module {
        bindings : bindings,
    } = module;
    
    let bindings2 = renamer.rename_bindings(bindings);
    
    Module {
        bindings : bindings2,
    }
}
pub fn abstract_module(module: Module<(Type, ~str)>) -> Module<(Type, ~str)> {
    each_binding(module,
        |name| name,
        |bind| {
            let Binding { name: name, expression: bind_expr } = bind;
            let mut variables = HashMap::new();
            let mut free_vars = HashSet::new();
            let e = free_variables(&mut variables, &mut free_vars, bind_expr);
            Binding { name: name, expression: e }
        })
}

pub fn each_binding<Ident, Ident2>(module: Module<Ident>, _trans: |Ident| -> Ident2, bind_f: |Binding<Ident>| -> Binding<Ident2>) -> Module<Ident2> {
    let Module {
        bindings : bindings,
    } = module;
    
    let bindings2 = bindings.move_iter().map(|x| bind_f(x)).collect();
    
    Module {
        bindings : bindings2,
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
}
