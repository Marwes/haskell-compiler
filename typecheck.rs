use std::hashmap::HashMap;
use lexer::Location;
use std::fmt;
use module::{Type, TypeVariable, TypeOperator, Expr, Identifier, Number, Apply, Lambda, Let, Typed, Alternative};


pub struct TypeEnvironment {
    namedTypes : HashMap<~str, @mut Type>,
    types : ~[@mut Type],
    variableIndex : TypeVariable
}

impl TypeEnvironment {
    pub fn new() -> TypeEnvironment {
        TypeEnvironment { namedTypes : HashMap::new(), types : ~[] , variableIndex : TypeVariable { id : 0 } }
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
                    TypeEnvironment::replace(t, subs); 
                }
            }
        }
    }

    pub fn typecheck(&mut self, expr : &mut Typed<Expr>) {
        *expr.typ = TypeVariable(self.variableIndex);
        self.variableIndex.id += 1;
        self.types.push(expr.typ);
        match &mut expr.expr {
            &Number(_) => {
                expr.typ = @mut TypeOperator(TypeOperator {name : ~"Int", types : ~[]});
            }
            &Identifier(ref name) => {
                match self.namedTypes.find(name) {
                    Some(t) => { expr.typ = (*t).clone(); }
                    None => { fail!("Undefined identifier " + *name); }
                }
            }
            &Apply(ref mut func, ref mut arg) => {
                self.typecheck(*func);
                self.typecheck(*arg);
                let mut funcType = TypeOperator(TypeOperator { name : ~"->", types : ~[(*arg.typ).clone(), TypeVariable(self.variableIndex)]});
                self.variableIndex.id += 1;
                let subs = unify(self, func.typ, &funcType);
                self.substitute(&subs);
                TypeEnvironment::replace(&mut funcType, &subs);
                *expr.typ = match funcType {
                    TypeOperator(t) => t.types[1],
                    _ => fail!("Can't happen")
                };
            }
            &Lambda(ref arg, ref mut body) => {
                fail!("Typechecking lambda are not implemented");
            }
            &Let(ref mut bindings, ref mut body) => {
                fail!("Typechecking Let are not implemented");
            }
        };
    }

    fn substitute(&mut self, subs : &HashMap<TypeVariable, Type>) {
        for t in self.types.iter() {
            TypeEnvironment::replace(*t, subs);
        }
    }

    fn addName(&mut self, name : ~str, t : @mut Type) {
        self.namedTypes.insert(name, t);
        self.addType(t);
    }

    fn addType(&mut self, t : @mut Type) {
        self.types.push(t);
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
pub fn let_(bindings : ~[(~str, ~Typed<Expr>)], expr : Typed<Expr>) -> Typed<Expr> {
    Typed::new(Let(bindings, ~expr))
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
    env.addName(~"add", add_type);
    env.typecheck(&mut expr);

    assert!(*expr.typ == unary_func);
}
