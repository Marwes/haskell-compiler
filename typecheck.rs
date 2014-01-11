use std::hashmap::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use module::{Type, TypeVariable, TypeOperator, Expr, Identifier, Number, Apply, Lambda, Let, Case, TypedExpr, Module, Alternative, Pattern, IdentifierPattern, NumberPattern, ConstructorPattern, Binding};
use Scope;
use graph::{Graph, VertexIndex, strongly_connected_components};

#[cfg(test)]
use parser::Parser;

type TypePtr = Rc<RefCell<Type>>;
fn new_ptr(t: Type) -> TypePtr {
    Rc::from_mut(RefCell::new(t))
}

pub struct TypeEnvironment {
    namedTypes : HashMap<~str, Rc<RefCell<Type>>>,
    types : ~[Rc<RefCell<Type>>],
    variableIndex : TypeVariable
}

struct TypeScope<'a> {
    scope: Scope<'a, Rc<RefCell<Type>>>,
    env: &'a mut TypeEnvironment,
    parent: Option<&'a TypeScope<'a>>,
    non_generic: ~[Rc<RefCell<Type>>]
}

impl TypeEnvironment {
    pub fn new() -> TypeEnvironment {
        let mut globals = HashMap::new();
        let int_type = &Type::new_op(~"Int", ~[]);
        let binop = new_ptr(function_type(int_type, &function_type(int_type, int_type)));
        globals.insert(~"primIntAdd", binop.clone());
        globals.insert(~"primIntSubtract", binop.clone());
        globals.insert(~"primIntMultiply", binop.clone());
        globals.insert(~"primIntDivide", binop.clone());
        globals.insert(~"primIntRemainder", binop.clone());
        let list_var = Type::new_var(-10);
        let list = Type::new_op(~"[]", ~[list_var.clone()]);
        globals.insert(~"[]", new_ptr(list.clone()));
        globals.insert(~":", new_ptr(function_type(&list_var, &function_type(&list, &list))));
        TypeEnvironment { namedTypes : globals, types : ~[] , variableIndex : TypeVariable { id : 0 } }
    }

    pub fn typecheck_module(&mut self, module: &mut Module) {
        for data_def in module.dataDefinitions.iter() {
            for constructor in data_def.constructors.iter() {
                self.namedTypes.insert(constructor.name.clone(), new_ptr(constructor.typ.clone()));
            }
        }
        let mut scope = TypeScope { env: self, scope: Scope::new(), non_generic: ~[], parent: None };
        scope.typecheck_mutually_recursive_bindings(module.bindings);
    }


    pub fn typecheck(&mut self, expr : &mut TypedExpr) {
        let mut scope = TypeScope { env: self, scope: Scope::new(), non_generic: ~[], parent: None };
        scope.typecheck(expr)
    }

    fn substitute(&mut self, subs : &HashMap<TypeVariable, Type>) {
        for t in self.types.iter() {
            let mut typ = t.borrow().borrow_mut();
            replace(typ.get(), subs);
        }
    }

    fn new_var(&mut self) -> Type {
        self.variableIndex.id += 1;
        TypeVariable(self.variableIndex)
    }
}

impl <'a> TypeScope<'a> {

    fn typecheck(&mut self, expr : &mut TypedExpr) {
        expr.typ.borrow().with_mut(|typ| *typ = self.env.new_var());
        self.env.types.push(expr.typ.clone());

        match &mut expr.expr {
            &Number(_) => {
                expr.typ.borrow().with_mut(|typ| *typ = TypeOperator(TypeOperator {name : ~"Int", types : ~[]}));
            }
            &Identifier(ref name) => {
                match self.fresh(*name) {
                    Some(t) => {
                        let mut typ = expr.typ.borrow().borrow_mut();
                        *typ.get() = t;
                    }
                    None => fail!("Undefined identifier '{}' at {}", *name, expr.location)
                }
            }
            &Apply(ref mut func, ref mut arg) => {
                self.typecheck(*func);
                self.typecheck(*arg);
                expr.typ.borrow().with_mut(|typ| {
                    let arg_type = arg.typ.borrow().with(|typ| typ.clone());
                    *typ = TypeOperator(TypeOperator {
                        name : ~"->", types : ~[arg_type, self.env.new_var()]
                    });
                });

                let func_type = func.typ.borrow().borrow();
                let expr_type = expr.typ.borrow().borrow();
                let subs = unify(self.env, func_type.get(), expr_type.get());
                self.env.substitute(&subs);
                expr.typ.borrow().with_mut(|typ| {
                    *typ = match expr_type.get() {
                        &TypeOperator(ref t) => t.types[1].clone(),
                        _ => fail!("Can't happen")
                    };
                });
                
            }
            &Lambda(ref arg, ref mut body) => {
                let argType = new_ptr(self.env.new_var());
                expr.typ.borrow().with_mut(|typ| {
                    let a = argType.borrow().borrow();
                    *typ = function_type(a.get(), &self.env.new_var());
                });
                let mut childScope = self.child();
                childScope.insert(arg.clone(), &argType);
                childScope.non_generic.push(argType);
                childScope.typecheck(*body);
                let mut expr_type = expr.typ.borrow().borrow_mut();
                match expr_type.get() {
                    &TypeOperator(ref mut op) => {
                        let t = body.typ.borrow().borrow();
                        op.types[1] = t.get().clone();
                    }
                    _ => fail!("This should never happen since a TypeOperator can never be turned to a TypeVariable (would be a type error)")
                }
            }
            &Let(ref mut bindings, ref mut body) => {
                let mut childScope = self.child();
                childScope.typecheck_mutually_recursive_bindings(*bindings);
                childScope.typecheck(*body);
                expr.typ = body.typ.clone();
            }
            &Case(ref mut case_expr, ref mut alts) => {
                self.typecheck(*case_expr);
                let match_type = case_expr.typ.borrow().borrow();
                self.typecheck_pattern(&alts[0].pattern, &mut (*match_type.get()).clone());
                self.typecheck(&mut alts[0].expression);
                let alt0_ = alts[0].expression.typ.clone();
                let alt0_type = alt0_.borrow().borrow();
                for alt in alts.mut_iter().skip(1) {
                    self.typecheck_pattern(&alt.pattern, &mut (*match_type.get()).clone());
                    self.typecheck(&mut alt.expression);
                    let mut alt_type = alt.expression.typ.borrow().borrow();
                    let subs = unify(self.env, alt_type.get(), alt0_type.get());
                    self.env.substitute(&subs);
                }
                expr.typ = alts[0].expression.typ.clone();
            }
        };
    }

    fn typecheck_pattern(&mut self, pattern: &Pattern, match_type: &mut Type) {
        match pattern {
            &IdentifierPattern(ref ident) => {
                let typ = new_ptr(self.env.new_var());
                self.insert(ident.clone(), &typ);
                {
                    let t = typ.borrow().borrow();
                    let subs = unify(self.env, t.get(), match_type);
                    self.env.substitute(&subs);
                    replace(match_type, &subs);
                }
                self.non_generic.push(typ);
            }
            &NumberPattern(_) => {
                fail!("Number pattern typechecking are not implemented");
            }
            &ConstructorPattern(ref ctorname, ref patterns) => {
                let mut t = self.fresh(*ctorname).unwrap();
                let data_type = get_returntype(&t);
                
                self.pattern_rec(0, *patterns, &mut t);

                let subs = unify(self.env, &data_type, match_type);
                self.env.substitute(&subs);
                replace(match_type, &subs);
            }
        }
    }

    fn pattern_rec(&mut self, i : uint, patterns: &[Pattern], func_type: &mut Type) {
        if i < patterns.len() {
            let p = &patterns[i];
            match func_type {
                &TypeOperator(ref mut op) => {
                    self.typecheck_pattern(p, &mut op.types[0]);
                    self.pattern_rec(i + 1, patterns, &mut op.types[1]);
                }
                _ => fail!("Any allowed constructor must be a type operator")
            }
        }
    }

    pub fn typecheck_mutually_recursive_bindings(&mut self, bindings: &mut[Binding]) {
        
        let graph = build_graph(bindings);
        let groups = strongly_connected_components(&graph);

        for group in groups.iter() {

            for index in group.iter() {
                let bindIndex = graph.get_vertex(*index).value;
                self.insert(bindings[bindIndex].name.clone(), &bindings[bindIndex].expression.typ);
            }
            
            for index in group.iter() {
                let bindIndex = graph.get_vertex(*index).value;
                let bind = &mut bindings[bindIndex];
                self.non_generic.push(bind.expression.typ.clone());
                self.typecheck(&mut bind.expression);
            }
            
            for index in group.iter() {
                let bindIndex = graph.get_vertex(*index).value;
                let bind = &mut bindings[bindIndex];
                self.non_generic.pop();
            }
        }
    }

    fn insert(&mut self, name: ~str, t : &Rc<RefCell<Type>>) {
        self.scope.insert(name, t.clone());
        self.env.types.push(t.clone());
    }
    fn find(&'a self, name: &str) -> Option<&'a Rc<RefCell<Type>>> {
        match self.scope.find(name) {
            Some(x) => Some(x),
            None => self.env.namedTypes.find_equiv(&name)
        }
    }
    fn fresh(&'a self, name: &str) -> Option<Type> {
        match self.find(name) {
            Some(x) => {
                let mut mapping = HashMap::new();
                let typ = x.borrow().borrow();
                Some(freshen(self, &mut mapping, typ.get()))
            }
            None => None
        }
    }

    fn is_generic(&'a self, var: &TypeVariable) -> bool {
        let found = self.non_generic.iter().any(|t| {
            let typ = t.borrow().borrow();
            occurs(var, typ.get())
        });
        if found {
            false
        }
        else {
            match self.parent {
                Some(p) => p.is_generic(var),
                None => true
            }
        }
    }

    fn child(&'a self) -> TypeScope<'a> {
        TypeScope { env: self.env, scope: self.scope.child(), non_generic: ~[], parent: Some(self) }
    }
}

fn get_returntype(typ: &Type) -> Type {
    match typ {
        &TypeOperator(ref op) => {
            if op.name == ~"->" {
                get_returntype(&op.types[1])
            }
            else {
                typ.clone()
            }
        }
        _ => typ.clone()
    }
}

fn occurs(type_var: &TypeVariable, inType: &Type) -> bool {
    match inType {
        &TypeVariable(var) => type_var.id == var.id,
        &TypeOperator(ref op) => op.types.iter().any(|t| occurs(type_var, t))
    }
}

fn freshen(env: &TypeScope, mapping: &mut HashMap<TypeVariable, Type>, typ: &Type) -> Type {
    match typ {
        &TypeVariable(ref id) => {
            if env.is_generic(id) {
                mapping.find_or_insert(*id, env.env.new_var()).clone()
            }
            else {
                typ.clone()
            }
        }
        &TypeOperator(ref op) => {
            let types = FromIterator::from_iterator(&mut op.types.iter().map(|t| freshen(env, mapping, t)));
            Type::new_op(op.name.clone(), types)
        }
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
                let mut t = TypeVariable(rid);
                replace(&mut t, subs);
                subs.insert(lid, t);
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
        (&TypeVariable(lid), &TypeOperator(_)) => {
            if (occurs(&lid, rhs)) {
                fail!("Recursive unification");
            }
            let mut t = (*rhs).clone();
            replace(&mut t, subs);
            subs.insert(lid, t);
        }
        _ => { unify_(env, subs, rhs, lhs); }
    }
}

fn build_graph(bindings: &[Binding]) -> Graph<uint> {
    let mut graph = Graph::new();
    let mut map = HashMap::new();
    for i in range(0, bindings.len()) {
        let index = graph.new_vertex(i);
        map.insert(bindings[i].name.clone(), index);
    }
    for bind in bindings.iter() {
        add_edges(&mut graph, &map, *map.get(&bind.name), &bind.expression);
    }
    graph
}

fn add_edges<T>(graph: &mut Graph<T>, map: &HashMap<~str, VertexIndex>, function_index: VertexIndex, expr: &TypedExpr) {
    match &expr.expr {
        &Identifier(ref n) => {
            match map.find_equiv(n) {
                Some(index) => graph.connect(function_index, *index),
                None => ()
            }
        }
        &Lambda(_, ref body) => {
            add_edges(graph, map, function_index, *body);
        }
        &Apply(ref f, ref a) => {
            add_edges(graph, map, function_index, *f);
            add_edges(graph, map, function_index, *a);
        }
        &Let(ref binds, ref body) => {
            add_edges(graph, map, function_index, *body);
            for bind in binds.iter() {
                add_edges(graph, map, function_index, &bind.expression);
            }
        }
        &Case(ref b, ref alts) => {
            add_edges(graph, map, function_index, *b);
            for alt in alts.iter() {
                add_edges(graph, map, function_index, &alt.expression);
            }
        }
        _ => ()
    }
}


pub fn function_type(func : &Type, arg : &Type) -> Type {
    TypeOperator(TypeOperator { name : ~"->", types : ~[func.clone(), arg.clone()]})
}

pub fn identifier(i : ~str) -> TypedExpr {
    TypedExpr::new(Identifier(i))
}

pub fn lambda(arg : ~str, body : TypedExpr) -> TypedExpr {
    TypedExpr::new(Lambda(arg, ~body))
}
pub fn number(i : int) -> TypedExpr {
    TypedExpr::new(Number(i))
}
pub fn apply(func : TypedExpr, arg : TypedExpr) -> TypedExpr {
    TypedExpr::new(Apply(~func, ~arg))
}
pub fn let_(bindings : ~[Binding], expr : TypedExpr) -> TypedExpr {
    TypedExpr::new(Let(bindings, ~expr))
}
pub fn case(expr : TypedExpr, alts: ~[Alternative]) -> TypedExpr {
    TypedExpr::new(Case(~expr, alts))
}


#[test]
fn test() {
    let mut env = TypeEnvironment::new();
    let n = ~TypedExpr::new(Identifier(~"add"));
    let num = ~TypedExpr::new(Number(1));
    let mut expr = TypedExpr::new(Apply(n, num));
    let type_int = TypeOperator(TypeOperator { name : ~"Int", types : ~[]});
    let unary_func = function_type(&type_int, &type_int);
    let add_type = new_ptr(function_type(&type_int, &unary_func));
    env.namedTypes.insert(~"add", add_type);
    env.typecheck(&mut expr);

    let expr_type = expr.typ.borrow().borrow();
    assert!(*expr_type.get() == unary_func);
}

#[test]
fn typecheck_lambda() {
    let mut env = TypeEnvironment::new();
    let type_int = TypeOperator(TypeOperator { name : ~"Int", types : ~[]});
    let unary_func = function_type(&type_int, &type_int);
    let add_type = new_ptr(function_type(&type_int, &unary_func));

    let mut expr = lambda(~"x", apply(apply(identifier(~"add"), identifier(~"x")), number(1)));
    env.namedTypes.insert(~"add", add_type);
    env.typecheck(&mut expr);

    let expr_type = expr.typ.borrow().borrow();
    assert_eq!(*expr_type.get(), unary_func);
}

#[test]
fn typecheck_let() {
    let mut env = TypeEnvironment::new();
    let type_int = TypeOperator(TypeOperator { name : ~"Int", types : ~[]});
    let unary_func = function_type(&type_int, &type_int);
    let add_type = new_ptr(function_type(&type_int, &unary_func));

    //let test x = add x in test
    let unary_bind = lambda(~"x", apply(apply(identifier(~"add"), identifier(~"x")), number(1)));
    let mut expr = let_(~[Binding { arity: 1, name: ~"test", expression: unary_bind, typeDecl: Default::default() }], identifier(~"test"));
    env.namedTypes.insert(~"add", add_type);
    env.typecheck(&mut expr);

    let expr_type = expr.typ.borrow().borrow();
    assert_eq!(*expr_type.get(), unary_func);
}

#[test]
fn typecheck_case() {
    let mut env = TypeEnvironment::new();
    let type_int = TypeOperator(TypeOperator { name : ~"Int", types : ~[]});
    let unary_func = function_type(&type_int, &type_int);
    let add_type = new_ptr(function_type(&type_int, &unary_func));

    let mut parser = Parser::new("case [] of { : x xs -> add x 2 ; [] -> 3}".chars());
    let mut expr = parser.expression_();
    env.namedTypes.insert(~"add", add_type);
    env.typecheck(&mut expr);

    let expr_type = expr.typ.borrow().borrow();
    assert_eq!(*expr_type.get(), type_int);
    match &expr.expr {
        &Case(ref case_expr, _) => {
            let case_type = case_expr.typ.borrow().borrow();
            assert_eq!(*case_type.get(), Type::new_op(~"[]", ~[Type::new_op(~"Int", ~[])]));
        }
        _ => fail!("typecheck_case")
    }
}

#[test]
fn typecheck_module() {
    let mut env = TypeEnvironment::new();

    let mut parser = Parser::new(
r"data Bool = True | False
test x = True".chars());
    let mut module = parser.module();
    env.typecheck_module(&mut module);

    let typ = function_type(&Type::new_var(0), &Type::new_op(~"Bool", ~[]));
    let bind_type0 = module.bindings[0].expression.typ.borrow().borrow();
    assert_eq!(*bind_type0.get(), typ);
}


#[test]
fn typecheck_let_recursive() {
    let mut env = TypeEnvironment::new();

    let mut parser = Parser::new(
r"let
    a = 0
    test = 1 : test2
    test2 = 2 : test
    b = test
in b".chars());
    let mut expr = parser.expression_();
    env.typecheck(&mut expr);

    
    let int_type = Type::new_op(~"Int", ~[]);
    let list_type = Type::new_op(~"[]", ~[int_type.clone()]);
    match &expr.expr {
        &Let(ref binds, ref body) => {
            assert_eq!(binds.len(), 4);
            assert_eq!(binds[0].name, ~"a");
            let bind_type0 = binds[0].expression.typ.borrow().borrow();
            assert_eq!(*bind_type0.get(), int_type);
            assert_eq!(binds[1].name, ~"test");
            let bind_type1 = binds[1].expression.typ.borrow().borrow();
            assert_eq!(*bind_type1.get(), list_type);
        }
        _ => fail!("Error")
    }
}
