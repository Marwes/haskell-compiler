use std::hashmap::HashMap;
use module::{Type, TypeVariable, TypeOperator, Expr, Identifier, Number, Apply, Lambda, Let, Case, Typed, Alternative, Binding};
use Scope;


pub struct TypeEnvironment {
    namedTypes : HashMap<~str, @mut Type>,
    types : ~[@mut Type],
    variableIndex : TypeVariable
}

struct TypeScope<'a> {
    scope: Scope<'a, @mut Type>,
    env: &'a mut TypeEnvironment,
    non_generic: ~[@mut Type]
}

impl TypeEnvironment {
    pub fn new() -> TypeEnvironment {
        let mut globals = HashMap::new();
        let int_type = &Type::new_op(~"Int", ~[]);
        let binop = @mut function_type(int_type, &function_type(int_type, int_type));
        globals.insert(~"primIntAdd", binop);
        globals.insert(~"primIntSubtract", binop);
        globals.insert(~"primIntMultiply", binop);
        globals.insert(~"primIntDivide", binop);
        globals.insert(~"primIntRemainder", binop);
        TypeEnvironment { namedTypes : globals, types : ~[] , variableIndex : TypeVariable { id : 0 } }
    }

    pub fn typecheck(&mut self, expr : &mut Typed<Expr>) {
        let mut scope = TypeScope { env: self, scope: Scope::new(), non_generic: ~[] };
        scope.typecheck(expr)
    }

    fn substitute(&mut self, subs : &HashMap<TypeVariable, Type>) {
        for t in self.types.iter() {
            replace(*t, subs);
        }
    }

    fn new_var(&mut self) -> Type {
        self.variableIndex.id += 1;
        TypeVariable(self.variableIndex)
    }
}

impl <'a> TypeScope<'a> {

    fn typecheck(&mut self, expr : &mut Typed<Expr>) {
        *expr.typ = self.env.new_var();
        self.env.types.push(expr.typ);

        match &mut expr.expr {
            &Number(_) => {
                expr.typ = @mut TypeOperator(TypeOperator {name : ~"Int", types : ~[]});
            }
            &Identifier(ref name) => {
                match self.find(*name) {
                    Some(t) => { expr.typ = (*t).clone(); }
                    None => { fail!("Undefined identifier " + *name); }
                }
            }
            &Apply(ref mut func, ref mut arg) => {
                self.typecheck(*func);
                self.typecheck(*arg);
                let mut funcType = TypeOperator(TypeOperator { name : ~"->", types : ~[(*arg.typ).clone(), self.env.new_var()]});
                let subs = unify(self.env, func.typ, &funcType);
                self.env.substitute(&subs);
                replace(&mut funcType, &subs);
                *expr.typ = match funcType {
                    TypeOperator(t) => t.types[1],
                    _ => fail!("Can't happen")
                };
            }
            &Lambda(ref arg, ref mut body) => {
                let argType = @mut self.env.new_var();
                *expr.typ = function_type(argType, &self.env.new_var());
                let mut childScope = self.child();
                childScope.insert(arg.clone(), argType);
                childScope.non_generic.push(argType);
                childScope.typecheck(*body);
                match &mut *expr.typ {
                    &TypeOperator(ref mut op) => op.types[1] = (*body.typ).clone(),
                    _ => fail!("This should never happen since a TypeOperator can never be turned to a TypeVariable (would be a type error)")
                }
            }
            &Let(ref mut bindings, ref mut body) => {
                let mut childScope = self.child();
                for bind in bindings.mut_iter() {
                    childScope.insert(bind.name.clone(), bind.expression.typ);
                    childScope.typecheck(&mut bind.expression);
                }
                childScope.typecheck(*body);
                expr.typ = body.typ;
            }
            &Case(_, _) => {
                fail!("Typechecking Case are not implemented");
            }
        };
    }

    fn insert(&mut self, name: ~str, t : @mut Type) {
        self.scope.insert(name, t);
        self.env.types.push(t);
    }
    fn find(&'a self, name: &str) -> Option<&'a @mut Type> {
        match self.scope.find(name) {
            Some(x) => Some(x),
            None => self.env.namedTypes.find_equiv(&name)
        }
    }

    fn child(&'a self) -> TypeScope<'a> {
        TypeScope { env: self.env, scope: self.scope.child(), non_generic: ~[] }
    }
}

fn replace(old : &mut Type, subs : &HashMap<TypeVariable, Type>) {
    match old {
        &TypeVariable(id) => {
            match subs.find(&id) {
                Some(new) => { *old = new.clone() }
                None => ()
            }
        }
        &TypeOperator(ref mut op) => {
            for t in op.types.mut_iter() {
                replace(t, subs); 
            }
        }
    }
}

fn unify(env : &mut TypeEnvironment, lhs : &Type, rhs : &Type) -> HashMap<TypeVariable, Type> {
    let mut subs = HashMap::new();
    unify_(env, &mut subs, lhs, rhs);
    subs
}
fn unify_(env : &mut TypeEnvironment, subs : &mut HashMap<TypeVariable, Type>, lhs : &Type, rhs : &Type) {
    match (lhs, rhs) {
        (&TypeVariable(lid), &TypeVariable(rid)) => {
            if lid != rid {
                subs.insert(lid, TypeVariable(rid));
            }
        }
        (&TypeOperator(ref l), &TypeOperator(ref r)) => {
            if l.name != r.name || l.types.len() != r.types.len() {
                fail!("Could not unify TypeOperators " + l.name + " and " + r.name);
            }
            for i in range(0, l.types.len()) {
                unify_(env, subs, &l.types[i], &r.types[i]);
            }
        }
        (&TypeVariable(lid), &TypeOperator(_)) => { subs.insert(lid, (*rhs).clone()); }
        _ => { unify_(env, subs, rhs, lhs); }
    }
}

pub fn function_type(func : &Type, arg : &Type) -> Type {
    TypeOperator(TypeOperator { name : ~"->", types : ~[func.clone(), arg.clone()]})
}

pub fn identifier(i : ~str) -> Typed<Expr> {
    Typed::new(Identifier(i))
}

pub fn lambda(arg : ~str, body : Typed<Expr>) -> Typed<Expr> {
    Typed::new(Lambda(arg, ~body))
}
pub fn number(i : int) -> Typed<Expr> {
    Typed::new(Number(i))
}
pub fn apply(func : Typed<Expr>, arg : Typed<Expr>) -> Typed<Expr> {
    Typed::new(Apply(~func, ~arg))
}
pub fn let_(bindings : ~[Binding], expr : Typed<Expr>) -> Typed<Expr> {
    Typed::new(Let(bindings, ~expr))
}
pub fn case(expr : Typed<Expr>, alts: ~[Alternative]) -> Typed<Expr> {
    Typed::new(Case(~expr, alts))
}


#[test]
fn test() {
    let mut env = TypeEnvironment::new();
    let n = ~Typed::new(Identifier(~"add"));
    let num = ~Typed::new(Number(1));
    let mut expr = Typed::new(Apply(n, num));
    let type_int = TypeOperator(TypeOperator { name : ~"Int", types : ~[]});
    let unary_func = function_type(&type_int, &type_int);
    let add_type = @mut function_type(&type_int, &unary_func);
    env.namedTypes.insert(~"add", add_type);
    env.typecheck(&mut expr);

    assert!(*expr.typ == unary_func);
}

#[test]
fn typecheck_lambda() {
    let mut env = TypeEnvironment::new();
    let n = ~Typed::new(Identifier(~"add"));
    let num = ~Typed::new(Number(1));
    let type_int = TypeOperator(TypeOperator { name : ~"Int", types : ~[]});
    let unary_func = function_type(&type_int, &type_int);
    let add_type = @mut function_type(&type_int, &unary_func);

    let mut expr = lambda(~"x", apply(apply(identifier(~"add"), identifier(~"x")), number(1)));
    env.namedTypes.insert(~"add", add_type);
    env.typecheck(&mut expr);

    assert_eq!(*expr.typ, unary_func);
}

#[test]
fn typecheck_let() {
    let mut env = TypeEnvironment::new();
    let n = ~Typed::new(Identifier(~"add"));
    let num = ~Typed::new(Number(1));
    let type_int = TypeOperator(TypeOperator { name : ~"Int", types : ~[]});
    let unary_func = function_type(&type_int, &type_int);
    let add_type = @mut function_type(&type_int, &unary_func);

    //let test x = add x in test
    let unary_bind = lambda(~"x", apply(apply(identifier(~"add"), identifier(~"x")), number(1)));
    let mut expr = let_(~[Binding { arity: 1, name: ~"test", expression: unary_bind, typeDecl: Default::default() }], identifier(~"test"));
    env.namedTypes.insert(~"add", add_type);
    env.typecheck(&mut expr);

    assert_eq!(*expr.typ, unary_func);
}
