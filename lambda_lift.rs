use collections::hashmap::{HashMap, HashSet};
use module::*;
use scoped_map::ScopedMap;

//Walks through an expression and notes all the free variables and for each lambda, adds the
//free variables to its arguments and performs an immediate application
//@variables All the local variables in scope, values are how many of the name there exists
//@free_vars The free variables for the returned expression
fn free_variables(variables: &mut HashMap<~str, int>, free_vars: &mut HashSet<~str>, input_expr: TypedExpr) -> TypedExpr {
    let TypedExpr { expr: expr, typ: typ, location: location } = input_expr;
    let e = match expr {
        Number(n) => Number(n),
        Rational(r) => Rational(r),
        Char(c) => Char(c),
        String(s) => String(s),
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
            let new_bindings: ~[Binding] = bindings.move_iter().map(
                |Binding { name: name, expression: bind_expr, typeDecl: typeDecl, arity:arity }| {
                free_vars2.clear();
                let e = free_variables(variables, &mut free_vars2, bind_expr);
                //free_vars2 is the free variables for this binding
                for v in free_vars2.iter() {
                    free_vars.insert(v.clone());
                }
                Binding{
                    name: name,
                    typeDecl: typeDecl,
                    arity: arity,
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
    };
    TypedExpr { expr:e, typ: typ, location: location }
}

fn abstract(free_vars: &HashSet<~str>, input_expr: TypedExpr) -> TypedExpr {

    fn mkTyped(e: Expr) -> TypedExpr {
        TypedExpr { typ: Default::default(), location: Location::eof(), expr: e }
    }

    let mut e = {
        let mut rhs = input_expr;
        for var in free_vars.iter() {
            rhs = mkTyped(Lambda(var.clone(), ~rhs));
        }
        let bind = Binding {
            name: "sc".to_owned(),
            arity: free_vars.len() + 1,
            typeDecl: Default::default(),
            expression: rhs
        };
        Let(~[bind], ~mkTyped(Identifier("sc".to_owned())))
    };
    for var in free_vars.iter() {
        e = Apply(~mkTyped(e), ~mkTyped(Identifier(var.clone())));
    }
    mkTyped(e)
}

#[deriving(Eq, TotalEq, Hash, Clone, Show)]
pub struct Unique {
    name: ~str,
    uid: uint
}

struct Renamer {
    uniques: ScopedMap<~str, Unique>,
    unique_id: uint
}
impl Renamer {

    fn rename_binding(&mut self, binding: Binding) -> Binding<Unique> {
        let Binding { name: name, expression: expression, typeDecl: typeDecl, arity: arity} = binding;
        Binding {
            name: self.make_unique(name),
            expression: self.rename(expression),
            typeDecl: typeDecl,
            arity: arity
        }
    }

    fn rename(&mut self, input_expr: TypedExpr) -> TypedExpr<Unique> {
        let TypedExpr { expr: expr, typ: typ, location: location } = input_expr;
        let e = match expr {
            Number(n) => Number(n),
            Rational(r) => Rational(r),
            Char(c) => Char(c),
            String(s) => String(s),
            Identifier(i) => Identifier(self.uniques.find(&i).map(|u| u.clone()).expect(format!("Undefined variable {}", i))),
            Apply(func, arg) => Apply(~self.rename(*func), ~self.rename(*arg)),
            Lambda(arg, body) => {
                self.uniques.enter_scope();
                let l = Lambda(self.make_unique(arg), ~self.rename(*body));
                self.uniques.exit_scope();
                l
            }
            Let(bindings, expr) => {
                self.uniques.enter_scope();
                let bs = bindings.move_iter().map(|b| self.rename_binding(b)).collect();
                let l = Let(bs, ~self.rename(*expr));
                self.uniques.exit_scope();
                l
            }
            Case(expr, alts) => {
                let a = alts.move_iter().map(|Alternative { pattern: pattern, expression: expression }| {
                    self.uniques.enter_scope();
                    let Located { location: location, node: node } = pattern;
                    let p = self.rename_pattern(node);
                    let a = Alternative {
                        pattern: Located { location: location, node: p },
                        expression: self.rename(expression)
                    };
                    self.uniques.exit_scope();
                    a
                }).collect();
                Case(~self.rename(*expr), a)
            }
        };
        TypedExpr { expr: e, typ: typ, location: location }
    }

    fn rename_pattern(&mut self, pattern: Pattern) -> Pattern<Unique> {
        match pattern {
            NumberPattern(i) => NumberPattern(i),
            ConstructorPattern(s, ps) => {
                let ps2 = ps.move_iter().map(|p| self.rename_pattern(p)).collect();
                ConstructorPattern(s, ps2)
            }
            IdentifierPattern(s) => IdentifierPattern(self.make_unique(s))
        }
    }

    fn make_unique(&mut self, name: ~str) -> Unique {
        self.unique_id += 1;
        let u = Unique { name: name.clone(), uid: self.unique_id};
        self.uniques.insert(name, u.clone());
        u
    }
}

pub fn rename_module(module: Module) -> Module<Unique> {
    let mut renamer = Renamer { uniques: ScopedMap::new(), unique_id: 0 };
    each_binding(module,
        |name| Unique { name: name, uid: 0, },
        |bind| renamer.rename_binding(bind))
}
pub fn abstract_module(module: Module) -> Module {
    each_binding(module,
        |name| name,
        |bind| {
            let Binding { name: name, expression: bind_expr, typeDecl: typeDecl, arity:arity } = bind;
            let mut variables = HashMap::new();
            let mut free_vars = HashSet::new();
            let e = free_variables(&mut variables, &mut free_vars, bind_expr);
            Binding { name: name, expression: e, typeDecl: typeDecl, arity:arity }
        })
}

pub fn each_binding<Ident, Ident2>(module: Module<Ident>, trans: |Ident| -> Ident2, bind_f: |Binding<Ident>| -> Binding<Ident2>) -> Module<Ident2> {
    let Module { name : name,
        bindings : bindings,
        typeDeclarations : typeDeclarations,
        classes : classes,
        instances : instances,
        dataDefinitions : dataDefinitions
    } = module;
    
    let instances2 = instances.move_iter().map(|instance| {
        let Instance {
            bindings : bindings,
            constraints : constraints,
            typ : typ,
            classname : classname
        } = instance;
        let binds = bindings.move_iter().map(|x| bind_f(x)).collect();
        Instance {
            bindings: binds,
            constraints: constraints,
            typ: typ,
            classname: classname
        }
    }).collect();
    let bindings2 = bindings.move_iter().map(|x| bind_f(x)).collect();
    
    Module { name : trans(name),
        bindings : bindings2,
        typeDeclarations : typeDeclarations,
        classes : classes,
        instances : instances2,
        dataDefinitions : dataDefinitions
    }
}


#[cfg(test)]
mod tests {
    use lambda_lift::*;
    use collections::hashmap::HashSet;
    use module::*;
    use parser::Parser;

    struct CheckUniques {
        found: HashSet<Unique>
    }

    impl Visitor<Unique> for CheckUniques {
        fn visit_binding(&mut self, bind: &Binding<Unique>) {
            assert!(self.found.insert(bind.name.clone()));
            self.visit_expr(&bind.expression);
        }
        fn visit_expr(&mut self, expr: &TypedExpr<Unique>) {
            match &expr.expr {
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
        let m = parser.module();
        let module = rename_module(m);
        (&mut visitor as &mut Visitor<Unique>).visit_module(&module);
    }

    fn check_args(expr: &TypedExpr, args: &[&str]) -> bool {
        match &expr.expr {
            &Lambda(ref arg, ref body) => arg.equiv(&args[0]) && check_args(*body, args.slice_from(1)),
            _ => args.len() == 0
        }
    }

    struct CheckAbstract {
        count: int
    }
    
    fn get_let<'a>(expr: &'a TypedExpr, args: &mut Vec<&'a str>) -> &'a TypedExpr {
        match &expr.expr {
            &Apply(ref f, ref arg) => {
                match &arg.expr {
                    &Identifier(ref i) => args.push(i.as_slice()),
                    _ => fail!("Expected identifier as argument")
                }
                get_let(*f, args)
            }
            _ => expr
        }
    }

    impl Visitor<~str> for CheckAbstract {
        fn visit_binding(&mut self, bind: &Binding) {
            if "f" == bind.name {
                let mut args = Vec::new();
                match &get_let(&bind.expression, &mut args).expr {
                    &Let(ref binds, ref body) => {
                        //Push the argument of the function itself
                        args.push("x");
                        assert!(check_args(&binds[0].expression, args.as_slice()));
                        assert_eq!(Identifier(binds[0].name.clone()), body.expr);
                    }
                    _ => assert!(false, "Expected Let, found {}", bind.expression)
                }
                self.count += 1;
            }
            else if "g" == bind.name {
                let mut args = Vec::new();
                match &get_let(&bind.expression, &mut args).expr {
                    &Let(ref binds, ref body) => {
                        args.push("y");
                        assert!(check_args(&binds[0].expression, args.as_slice()));
                        assert_eq!(Identifier(binds[0].name.clone()), body.expr);
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
        let m = parser.module();
        let module = abstract_module(m);
        (&mut visitor as &mut Visitor<~str>).visit_module(&module);
        assert_eq!(visitor.count, 2);
    }
}
