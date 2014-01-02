use std::hashmap::HashMap;

#[deriving(Clone)]
#[deriving(Eq)]
#[deriving(ToStr)]
pub enum Type {
    Variable(int),
    Operator(~str, ~[Type])
}

pub struct TypedExpr {
    expr : Expr<~TypedExpr>,
    typ : @mut Type
}

impl TypedExpr {
    pub fn new(expr : Expr<~TypedExpr>) -> TypedExpr {
        TypedExpr { expr : expr, typ : @mut Variable(0) }
    }
}

pub enum Expr<T> {
    Identifier(~str),
    Apply(T, T),
    Number(int),
    Lambda(~str, T),
    Let(~[(~str, T)], T)
}

pub struct TypeEnvironment {
    namedTypes : HashMap<~str, @mut Type>,
    types : ~[@mut Type],
    variableIndex : int
}

impl TypeEnvironment {
    pub fn new() -> TypeEnvironment {
        TypeEnvironment { namedTypes : HashMap::new(), types : ~[] , variableIndex : 0 }
    }

    fn replace(old : &mut Type, subs : &HashMap<int, Type>) {
        match old {
            &Variable(id) => {
                match subs.find(&id) {
                    Some(new) => { *old = new.clone() }
                    None => ()
                }
            }
            &Operator(_, ref mut oldTypes) => {
                for t in oldTypes.mut_iter() {
                    TypeEnvironment::replace(t, subs); 
                }
            }
        }
    }

    pub fn typecheck(&mut self, expr : &mut TypedExpr) {
        *expr.typ = Variable(self.variableIndex);
        self.variableIndex += 1;
        self.types.push(expr.typ);
        match &mut expr.expr {
            &Number(_) => {
                expr.typ = @mut Operator(~"Int", ~[]);
            }
            &Identifier(ref name) => {
                match self.namedTypes.find(name) {
                    Some(t) => { expr.typ = (*t).clone(); }
                    None => { fail!("Undefined identifier " + *name); }
                }
            }
            &Apply(ref mut func, ref mut arg) => {
                println!("Applying");
                self.typecheck(*func);
                self.typecheck(*arg);
                let mut funcType = Operator(~"->", ~[(*arg.typ).clone(), Variable(self.variableIndex)]);
                self.variableIndex += 1;
                let subs = unify(self, func.typ, &funcType);
                self.substitute(&subs);
                TypeEnvironment::replace(&mut funcType, &subs);
                *expr.typ = match funcType {
                    Operator(_, t) => t[1],
                    _ => fail!("Can't happen")
                };
            }
            _ => { () }
        };
    }

    fn substitute(&mut self, subs : &HashMap<int, Type>) {
        //println!("Substituting {:?}", subs);
        for t in self.types.iter() {
            println!("Type : {:?}", *t);
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

fn unify(env : &mut TypeEnvironment, lhs : &Type, rhs : &Type) -> HashMap<int, Type> {
    let mut subs = HashMap::new();
    unify_(env, &mut subs, lhs, rhs);
    subs
}
fn unify_(env : &mut TypeEnvironment, subs : &mut HashMap<int, Type>, lhs : &Type, rhs : &Type) {
    
    //println!("Unifying {:?} and {:?}", lhs, rhs);
    match (lhs, rhs) {
        (&Variable(lid), &Variable(rid)) => {
            if lid != rid {
                subs.insert(lid, Variable(rid));
            }
        }
        (&Operator(ref lName, ref lTypes), &Operator(ref rName, ref rTypes)) => {
            if *lName != *rName || lTypes.len() != rTypes.len() {
                fail!("Could not unify Operators " + *lName + " and " + *rName);
            }
            for i in range(0, lTypes.len()) {
                unify_(env, subs, &lTypes[i], &rTypes[i]);
            }
        }
        (&Variable(lid), &Operator(_, _)) => { subs.insert(lid, (*rhs).clone()); }
        _ => { unify_(env, subs, rhs, lhs); }
    }
}

pub fn function_type(func : &Type, arg : &Type) -> Type {
    Operator(~"->", ~[func.clone(), arg.clone()])
}

#[test]
fn test() {
    let mut env = TypeEnvironment::new();
    let n = ~TypedExpr::new(Identifier(~"add"));
    let num = ~TypedExpr::new(Number(1));
    let mut expr = TypedExpr::new(Apply(n, num));
    let type_int = Operator(~"Int", ~[]);
    let unary_func = function_type(&type_int, &type_int);
    let add_type = @mut function_type(&type_int, &unary_func);
    env.addName(~"add", add_type);
    env.typecheck(&mut expr);

    assert!(*expr.typ == unary_func);
}
