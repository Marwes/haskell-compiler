use std::hashmap::HashMap;
use module::{TypeVariable, TypeOperator, Identifier, Number, Rational, Apply, Lambda, Let, Case, TypedExpr, Module, Pattern, IdentifierPattern, NumberPattern, ConstructorPattern, Binding, TypeDeclaration};
use graph::{Graph, VertexIndex, strongly_connected_components};

pub use lexer::Location;
pub use module::Type;

#[cfg(test)]
use module::Alternative;

///Trait which can be implemented by types where types can be looked up by name
pub trait Types {
    fn find_type<'a>(&'a self, name: &str) -> Option<&'a Type>;
}

impl Types for Module {
    fn find_type<'a>(&'a self, name: &str) -> Option<&'a Type> {
        for bind in self.bindings.iter() {
            if bind.name.equiv(&name) {
                return Some(&bind.expression.typ);
            }
        }

        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                if decl.name.equiv(&name) {
                    return Some(&decl.typ);
                }
            }
        }
        for data in self.dataDefinitions.iter() {
            for ctor in data.constructors.iter() {
                if ctor.name.equiv(&name) {
                    return Some(&ctor.typ);
                }
            }
        }
        return None;
    }
}

pub struct TypeEnvironment<'a> {
    assemblies: ~[&'a Types],
    namedTypes : HashMap<~str, Type>,
    types : ~[Type],
    constraints: HashMap<TypeVariable, ~[~str]>,
    instances: ~[TypeOperator],
    variableIndex : TypeVariable
}

struct TypeScope<'a, 'b> {
    vars: ~[(~str, Type)],
    env: &'a mut TypeEnvironment<'b>,
    parent: Option<&'a TypeScope<'a, 'b>>,
    non_generic: ~[Type]
}

#[deriving(Clone)]
struct Substitution {
    subs: HashMap<TypeVariable, Type>,
    constraints: HashMap<TypeVariable, ~[~str]>
}

///Signals that a type error has occured and the top level types as well as the location is needed
condition! {
    type_error: () -> (Location, Type, Type);
}


impl <'a> TypeEnvironment<'a> {

    ///Creates a new TypeEnvironment and adds all the primitive types
    pub fn new() -> TypeEnvironment {
        let mut globals = HashMap::new();
        let int_type = &Type::new_op(~"Int", ~[]);
        {
            let binop = function_type(int_type, &function_type(int_type, int_type));
            globals.insert(~"primIntAdd", binop.clone());
            globals.insert(~"primIntSubtract", binop.clone());
            globals.insert(~"primIntMultiply", binop.clone());
            globals.insert(~"primIntDivide", binop.clone());
            globals.insert(~"primIntRemainder", binop.clone());
        }
        {
            let binop = function_type(int_type, &function_type(int_type, &Type::new_op(~"Bool", ~[])));
            globals.insert(~"primIntEQ", binop.clone());
            globals.insert(~"primIntLT", binop.clone());
            globals.insert(~"primIntLE", binop.clone());
            globals.insert(~"primIntGT", binop.clone());
            globals.insert(~"primIntGE", binop.clone());
        }
        let list_var = Type::new_var(-10);
        let list = Type::new_op(~"[]", ~[list_var.clone()]);
        globals.insert(~"[]", list.clone());
        globals.insert(~":", function_type(&list_var, &function_type(&list, &list)));
        TypeEnvironment {
            assemblies: ~[],
            namedTypes : globals,
            types : ~[] ,
            constraints: HashMap::new(),
            instances: ~[],
            variableIndex : TypeVariable { id : 0 } }
    }

    ///Typechecks a module by updating all the types in place
    pub fn typecheck_module(&mut self, module: &mut Module) {
        for data_def in module.dataDefinitions.mut_iter() {
            let mut subs = Substitution { subs: HashMap::new(), constraints: HashMap::new() };
            {
                let scope = TypeScope { env: self, vars: ~[], non_generic: ~[], parent: None };
                freshen(&scope, &mut subs.subs, &mut data_def.typ);
            }
            for constructor in data_def.constructors.mut_iter() {
                replace(&mut self.constraints, &mut constructor.typ, &subs);
                self.namedTypes.insert(constructor.name.clone(), constructor.typ.clone());
            }
        }
        for class in module.classes.mut_iter() {
            //Instantiate a new variable and replace all occurances of the class variable with this
            let replaced = class.variable;
            let new = self.new_var();
            class.variable = new.var().clone();

            for type_decl in class.declarations.mut_iter() {
                replace_var(&mut type_decl.typ, &replaced, &new);
                self.freshen_declaration(type_decl);
                self.namedTypes.insert(type_decl.name.clone(), type_decl.typ.clone());
            }
            self.constraints.insert(class.variable, ~[class.name.clone()]);
        }
        for instance in module.instances.iter() {
            self.instances.push(TypeOperator { name: instance.classname.clone(),
                types: ~[TypeOperator(instance.typ.clone())]});
        }
        
        for type_decl in module.typeDeclarations.mut_iter() {
            self.freshen_declaration(type_decl);

            match module.bindings.mut_iter().find(|bind| bind.name == type_decl.name) {
                Some(bind) => {
                    bind.typeDecl = type_decl.clone();
                }
                None => fail!("Error: Type declaration for '{}' has no binding", type_decl.name)
            }
        }

        {
            let mut scope = TypeScope { env: self, vars: ~[], non_generic: ~[], parent: None };
            let mut subs = Substitution { subs: HashMap::new(), constraints: HashMap::new() }; 
            scope.typecheck_mutually_recursive_bindings(&mut subs, module.bindings);
        }
        for bind in module.bindings.iter() {
            self.namedTypes.insert(bind.name.clone(), bind.expression.typ.clone());
        }
    }

    pub fn typecheck(&mut self, expr : &mut TypedExpr) {
        let mut subs = Substitution { subs: HashMap::new(), constraints: HashMap::new() }; 
        {
            let mut scope = TypeScope { env: self, vars: ~[], non_generic: ~[], parent: None };
            scope.typecheck(expr, &mut subs);
        }
        self.substitute(&mut subs, expr);
    }

    pub fn find(&'a self, ident: &str) -> Option<&'a Type> {
        self.namedTypes.find_equiv(&ident).or_else(|| {
            for types in self.assemblies.iter() {
                let v = types.find_type(ident);
                if v != None {
                    return v;
                }
            }
            None
        })
    }

    ///Finds all the constraints for a type
    pub fn find_constraints(&self, typ: &Type) -> ~[TypeOperator] {
        let mut constraints : ~[TypeOperator] = ~[];
        each_type(typ,
        |var| {
            match self.constraints.find(var) {
                Some(cons) => {
                    for c in cons.iter() {
                        if constraints.iter().find(|x| x.name == *c) == None {
                            constraints.push(TypeOperator { name: c.clone(), types: ~[TypeVariable(*var)] });
                        }
                    }
                }
                None => ()
            }
        },
        |_| ());
        constraints
    }
    
    ///Searches through a type, comparing it with the type on the identifier, returning all the specialized constraints
    pub fn find_specialized_instances(&self, name: &str, actual_type: &Type) -> ~[TypeOperator] {
        match self.find(name) {
            Some(typ) => {
                let mut constraints = ~[];
                self.find_specialized(&mut constraints, actual_type, typ);
                constraints
            }
            None => fail!("Could not find '{}' in type environment", name)
        }
    }
    fn find_specialized(&self, constraints: &mut ~[TypeOperator], actual_type: &Type, typ: &Type) {
        match (actual_type, typ) {
            (&TypeOperator(_), &TypeVariable(ref var)) => {
                match self.constraints.find(var) {
                    Some(cons) => {
                        for c in cons.iter() {
                            if constraints.iter().find(|x| x.name == *c) == None {
                                constraints.push(TypeOperator { name: c.clone(), types: ~[actual_type.clone()] });
                            }
                        }
                    }
                    None => ()
                }
            }
            (&TypeOperator(ref actual_op), &TypeOperator(ref op)) => {
                for ii in range(0, actual_op.types.len()) {
                    self.find_specialized(constraints, &actual_op.types[ii], &op.types[ii]);
                }
            }
            _ => ()
        }
    }

    fn freshen_declaration(&mut self, decl: &mut TypeDeclaration) {
        let mut subs = Substitution { subs: HashMap::new(), constraints: HashMap::new() }; 
        for constraint in decl.context.mut_iter() {
            let new = self.new_var();
            constraint.types[0] = new.clone();
            let old = constraint.types[0].var();
            subs.subs.insert(old.clone(), new);
        }
        replace(&mut self.constraints, &mut decl.typ, &subs);
    }

    ///Applies a substitution on all global types
    fn apply(&mut self, subs: &Substitution) {
        for (_, typ) in self.namedTypes.mut_iter() {
            replace(&mut self.constraints, typ, subs);
        }
    }

    ///Walks through an expression and applies the substitution on each of its types
    fn substitute(&mut self, subs : &Substitution, expr: &mut TypedExpr) {
        replace(&mut self.constraints, &mut expr.typ, subs);
        match &mut expr.expr {
            &Apply(ref mut func, ref mut arg) => {
                self.substitute(subs, *func);
                self.substitute(subs, *arg);
            }
            &Let(ref mut bindings, ref mut let_expr) => {
                for bind in bindings.mut_iter() {
                    self.substitute(subs, &mut bind.expression);
                }
                self.substitute(subs, *let_expr);
            }
            &Case(ref mut case_expr, ref mut alts) => {
                self.substitute(subs, *case_expr);
                for alt in alts.mut_iter() {
                    self.substitute(subs, &mut alt.expression);
                }
            }
            &Lambda(_, ref mut body) => self.substitute(subs, *body),
            _ => ()
        }
    }

    ///Returns whether the type 'op' has an instance for 'class'
    fn has_instance(&self, class: &str, op: &TypeOperator) -> bool {
        for typ in self.instances.iter() {
            match &typ.types[0] {
                &TypeOperator(ref other) => {
                    if typ.name.equiv(&class) && other == op {
                        return true;
                    }
                }
                _ => ()
            }
        }
        false
    }

    fn new_var(&mut self) -> Type {
        self.variableIndex.id += 1;
        TypeVariable(self.variableIndex)
    }
}
#[unsafe_destructor]
impl <'a, 'b> Drop for TypeScope<'a, 'b> {
    fn drop(&mut self) {
        while self.vars.len() > 0 {
            let (name, typ) = self.vars.pop();
            self.env.namedTypes.insert(name, typ);
        }
    }
}

impl <'a, 'b> TypeScope<'a, 'b> {

    fn apply(&mut self, subs: &Substitution) {
        self.env.apply(subs)
    }

    fn typecheck(&mut self, expr : &mut TypedExpr, subs: &mut Substitution) {
        if expr.typ == Type::new_var(0) {
            expr.typ = self.env.new_var();
        }

        match &mut expr.expr {
            &Number(_) => {
                expr.typ = TypeOperator(TypeOperator {name : ~"Int", types : ~[]});
            }
            &Rational(_) => {
                expr.typ = TypeOperator(TypeOperator {name : ~"Double", types : ~[]});
            }
            &Identifier(ref name) => {
                match self.fresh(*name) {
                    Some(t) => {
                        expr.typ = t;
                    }
                    None => fail!("Undefined identifier '{}' at {}", *name, expr.location)
                }
            }
            &Apply(ref mut func, ref mut arg) => {
                self.typecheck(*func, subs);
                replace(&mut self.env.constraints, &mut func.typ, subs);
                self.typecheck(*arg, subs);
                replace(&mut self.env.constraints, &mut arg.typ, subs);
                expr.typ = TypeOperator(TypeOperator {
                        name : ~"->", types : ~[arg.typ.clone(), self.env.new_var()]
                    });
                unify_location(self.env, subs, &expr.location, &mut func.typ, &mut expr.typ);
                replace(&mut self.env.constraints, &mut expr.typ, subs);
                expr.typ = match &expr.typ {
                    &TypeOperator(ref t) => t.types[1].clone(),
                    _ => fail!("Can't happen")
                };
            }
            &Lambda(ref arg, ref mut body) => {
                let argType = self.env.new_var();
                expr.typ = function_type(&argType, &self.env.new_var());
                {
                    let mut childScope = self.child();
                    childScope.insert(arg.clone(), &argType);
                    childScope.non_generic.push(argType.clone());
                    childScope.typecheck(*body, subs);
                }
                replace(&mut self.env.constraints, &mut expr.typ, subs);
                match &mut expr.typ {
                    &TypeOperator(ref mut op) => {
                        op.types[1] = body.typ.clone();
                    }
                    _ => fail!("This should never happen since a TypeOperator can never be turned to a TypeVariable (would be a type error)")
                }
            }
            &Let(ref mut bindings, ref mut body) => {
                {
                    let mut childScope = self.child();
                    childScope.typecheck_mutually_recursive_bindings(subs, *bindings);
                    childScope.apply(subs);
                    childScope.typecheck(*body, subs);
                }
                replace(&mut self.env.constraints, &mut body.typ, subs);
                expr.typ = body.typ.clone();
            }
            &Case(ref mut case_expr, ref mut alts) => {
                self.typecheck(*case_expr, subs);
                let mut match_type = case_expr.typ.clone();
                self.typecheck_pattern(subs, &alts[0].pattern, &mut match_type);
                self.typecheck(&mut alts[0].expression, subs);
                let mut alt0_ = alts[0].expression.typ.clone();
                for alt in alts.mut_iter().skip(1) {
                    self.typecheck_pattern(subs, &alt.pattern, &mut match_type);
                    self.typecheck(&mut alt.expression, subs);
                    unify_location(self.env, subs, &alt.expression.location, &mut alt0_, &mut alt.expression.typ);
                    replace(&mut self.env.constraints, &mut alt.expression.typ, subs);
                }
                replace(&mut self.env.constraints, &mut alts[0].expression.typ, subs);
                replace(&mut self.env.constraints, &mut case_expr.typ, subs);
                expr.typ = alts[0].expression.typ.clone();
            }
        };
    }

    fn typecheck_pattern(&mut self, subs: &mut Substitution, pattern: &Pattern, match_type: &mut Type) {
        match pattern {
            &IdentifierPattern(ref ident) => {
                let mut typ = self.env.new_var();
                self.insert(ident.clone(), &typ);
                {
                    unify(self.env, subs, &mut typ, match_type);
                    replace(&mut self.env.constraints, match_type, subs);
                }
                self.non_generic.push(typ.clone());
            }
            &NumberPattern(_) => {
                fail!("Number pattern typechecking are not implemented");
            }
            &ConstructorPattern(ref ctorname, ref patterns) => {
                let mut t = self.fresh(*ctorname).unwrap();
                let mut data_type = get_returntype(&t);
                
                self.pattern_rec(0, subs, *patterns, &mut t);

                unify(self.env, subs, &mut data_type, match_type);
                replace(&mut self.env.constraints, match_type, subs);
            }
        }
    }

    fn pattern_rec(&mut self, i : uint, subs: &mut Substitution, patterns: &[Pattern], func_type: &mut Type) {
        if i < patterns.len() {
            let p = &patterns[i];
            match func_type {
                &TypeOperator(ref mut op) => {
                    self.typecheck_pattern(subs, p, &mut op.types[0]);
                    self.pattern_rec(i + 1, subs, patterns, &mut op.types[1]);
                }
                _ => fail!("Any allowed constructor must be a type operator")
            }
        }
    }

    pub fn typecheck_mutually_recursive_bindings(&mut self, subs: &mut Substitution, bindings: &mut[Binding]) {
        
        let graph = build_graph(bindings);
        let groups = strongly_connected_components(&graph);

        for i in range(0, groups.len()) {
            let group = &groups[i];
            for index in group.iter() {
                let bindIndex = graph.get_vertex(*index).value;
                let bind = &mut bindings[bindIndex];
                bind.expression.typ = self.env.new_var();
                self.insert(bind.name.clone(), &bind.expression.typ);
                if bind.typeDecl.typ == Type::new_var(0) {
                    bind.typeDecl.typ = self.env.new_var();
                }
            }
            
            for index in group.iter() {
                {
                    let bindIndex = graph.get_vertex(*index).value;
                    let bind = &mut bindings[bindIndex];
                    self.non_generic.push(bind.expression.typ.clone());
                    let type_var = bind.expression.typ.var().clone();
                    self.typecheck(&mut bind.expression, subs);
                    unify_location(self.env, subs, &bind.expression.location, &mut bind.typeDecl.typ, &mut bind.expression.typ);
                    subs.subs.insert(type_var, bind.expression.typ.clone());
                    self.apply(subs);
                }
            }
            
            for index in group.iter() {
                let bindIndex = graph.get_vertex(*index).value;
                let bind = &mut bindings[bindIndex];
                self.non_generic.pop();
                self.env.substitute(subs, &mut bind.expression);
                bind.typeDecl.typ = bind.expression.typ.clone();
                bind.typeDecl.context = self.env.find_constraints(&bind.typeDecl.typ);
            }
        }
    }

    fn insert(&mut self, name: ~str, t : &Type) {
        match self.env.namedTypes.pop(&name) {
            Some(typ) => self.vars.push((name.clone(), typ)),
            None => ()
        }
        self.env.namedTypes.insert(name, t.clone());
    }
    fn find(&'a self, name: &str) -> Option<&'a Type> {
        self.env.find(name)
    }

    ///Instantiates new typevariables for every typevariable in the type found at 'name'
    fn fresh(&'a self, name: &str) -> Option<Type> {
        match self.find(name) {
            Some(x) => {
                let mut mapping = HashMap::new();
                let typ = x;
                Some(freshen(self, &mut mapping, typ))
            }
            None => None
        }
    }

    fn is_generic(&'a self, var: &TypeVariable) -> bool {
        let found = self.non_generic.iter().any(|t| {
            let typ = t;
            occurs(var, typ)
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

    fn child(&'a self) -> TypeScope<'a, 'b> {
        TypeScope { env: self.env, vars: ~[], non_generic: ~[], parent: Some(self) }
    }
}

fn replace_var(typ: &mut Type, var: &TypeVariable, replacement: &Type) {
    let new = match typ {
        &TypeVariable(ref v) => {
            if v == var {
                Some(replacement)
            }
            else {
                None
            }
        }
        &TypeOperator(ref mut op) => {
            for t in op.types.mut_iter(){
                replace_var(t, var, replacement);
            }
            None
        }
    };
    match new {
        Some(x) => *typ = x.clone(),
        None => ()
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

///Update the constraints when replacing the variable 'old' with 'new'
fn update_constraints(constraints: &mut HashMap<TypeVariable, ~[~str]>, old: &TypeVariable, new: &Type, subs: &Substitution) {
    match new {
        &TypeVariable(new_var) => {
            match subs.constraints.find(old) {
                Some(subs_constraints) => {
                    let to_update = constraints.find_or_insert(new_var, ~[]);
                    for c in subs_constraints.iter() {
                        if to_update.iter().find(|x| *x == c) == None {
                            to_update.push(c.clone());
                        }
                    }
                }
                None => ()
            }
        }
        _ => ()
    }
}

///Replace all typevariables using the substitution 'subs'
fn replace(constraints: &mut HashMap<TypeVariable, ~[~str]>, old : &mut Type, subs : &Substitution) {
    match old {
        &TypeVariable(id) => {
            match subs.subs.find(&id) {
                Some(new) => {
                    *old = new.clone();
                    update_constraints(constraints, &id, new, subs);
                }
                None => ()
            }
        }
        &TypeOperator(ref mut op) => {
            for t in op.types.mut_iter() {
                replace(constraints, t, subs); 
            }
        }
    }
}

///Checks whether a typevariable occurs in another type
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
                let new = env.env.new_var();
                let maybe_constraints = match env.env.constraints.find(id) {
                    Some(constraints) => Some(constraints.clone()),
                    None => None
                };
                match (maybe_constraints, &new) {
                    (Some(c), &TypeVariable(newid)) => { env.env.constraints.insert(newid, c); }
                    _ => ()
                }
                mapping.find_or_insert(*id, new).clone()
            }
            else {
                typ.clone()
            }
        }
        &TypeOperator(ref op) => {
            let types = op.types.iter().map(|t| freshen(env, mapping, t)).collect();
            Type::new_op(op.name.clone(), types)
        }
    }
}

///Takes two types and attempts to make them the same type
fn unify_location(env: &mut TypeEnvironment, subs: &mut Substitution, location: &Location, lhs: &mut Type, rhs: &mut Type) {
    type_error::cond.trap(|_| (location.clone(), lhs.clone(), rhs.clone())).inside(|| {
        unify_(env, subs, lhs, rhs);
        
        let subs2 = subs.clone();
        for (_, ref mut typ) in subs.subs.mut_iter() {
            replace(&mut env.constraints, *typ, &subs2);
        }
    })
}

fn unify(env : &mut TypeEnvironment, subs: &mut Substitution, lhs : &mut Type, rhs : &mut Type) {
    unify_location(env, subs, &Location { column: -1, row:-1, absolute:-1 }, lhs, rhs)
}

fn unify_(env : &mut TypeEnvironment, subs : &mut Substitution, lhs : &mut Type, rhs : &mut Type) {
    match (&lhs, &rhs) {
        (& &TypeVariable(ref lid), & &TypeVariable(ref rid)) => {
            if lid != rid {
                let mut t = TypeVariable(rid.clone());
                replace(&mut env.constraints, &mut t, subs);
                subs.subs.insert(lid.clone(), t);
                match env.constraints.pop(lid) {
                    Some(constraints) => { subs.constraints.insert(lid.clone(), constraints); }
                    None => ()
                }
            }
        }
        (& &TypeOperator(ref mut l), & &TypeOperator(ref mut r)) => {
            if l.name != r.name || l.types.len() != r.types.len() {
                let (location, l, r) = type_error::cond.raise(());
                fail!("{} Error: Could not unify types {}\nand\n{}", location, l, r)
            }
            for i in range(0, l.types.len()) {
                unify_(env, subs, &mut l.types[i], &mut r.types[i]);
                if i < l.types.len() - 1 {
                    replace(&mut env.constraints, &mut l.types[i+1], subs);
                    replace(&mut env.constraints, &mut r.types[i+1], subs);
                }
            }
        }
        (& &TypeVariable(ref lid), & &TypeOperator(ref op)) => {
            if (occurs(lid, rhs)) {
                let (location, l, r) = type_error::cond.raise(());
                fail!("{} Error: Recursive unification between {}\nand\n{}", location, l, r);
            }
            let mut t = (*rhs).clone();
            replace(&mut env.constraints, &mut t, subs);
            //Check that the type operator has an instance for all the constraints of the variable
            match env.constraints.find(lid) {
                Some(constraints) => {
                    for c in constraints.iter() {
                        if !env.has_instance(*c, op) {
                            let (location, l, r) = type_error::cond.raise(());
                            fail!("{} Error: No instance of class {} was found for {} when unifying {}\nand\n{}", location, *c, *op, l, r);
                        }
                    }
                }
                None => ()
            }
            subs.subs.insert(lid.clone(), t);
        }
        (lhs, rhs) => { unify_(env, subs, *rhs, *lhs); }
    }
}

///Creates a graph containing a vertex for each binding and edges for each 
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

fn each_type(typ: &Type, var_fn: |&TypeVariable|, op_fn: |&TypeOperator|) {
    each_type_(typ, &var_fn, &op_fn);
}
fn each_type_(typ: &Type, var_fn: &|&TypeVariable|, op_fn: &|&TypeOperator|) {
    match typ {
        &TypeVariable(ref var) => (*var_fn)(var),
        &TypeOperator(ref op) => {
            (*op_fn)(op);
            for t in op.types.iter() {
                each_type_(t, var_fn, op_fn);
            }
        }
    }
}

pub fn function_type(func : &Type, arg : &Type) -> Type {
    TypeOperator(TypeOperator { name : ~"->", types : ~[func.clone(), arg.clone()]})
}

#[cfg(test)]
pub fn identifier(i : ~str) -> TypedExpr {
    TypedExpr::new(Identifier(i))
}
#[cfg(test)]
pub fn lambda(arg : ~str, body : TypedExpr) -> TypedExpr {
    TypedExpr::new(Lambda(arg, ~body))
}
#[cfg(test)]
pub fn number(i : int) -> TypedExpr {
    TypedExpr::new(Number(i))
}
#[cfg(test)]
pub fn rational(i : f64) -> TypedExpr {
    TypedExpr::new(Rational(i))
}
#[cfg(test)]
pub fn apply(func : TypedExpr, arg : TypedExpr) -> TypedExpr {
    TypedExpr::new(Apply(~func, ~arg))
}
#[cfg(test)]
pub fn let_(bindings : ~[Binding], expr : TypedExpr) -> TypedExpr {
    TypedExpr::new(Let(bindings, ~expr))
}
#[cfg(test)]
pub fn case(expr : TypedExpr, alts: ~[Alternative]) -> TypedExpr {
    TypedExpr::new(Case(~expr, alts))
}

#[cfg(test)]
mod test {
use module::*;
use typecheck::*;

use parser::Parser;
use std::io::File;
use std::str::from_utf8;

#[test]
fn application() {
    let mut env = TypeEnvironment::new();
    let n = ~TypedExpr::new(Identifier(~"add"));
    let num = ~TypedExpr::new(Number(1));
    let mut expr = TypedExpr::new(Apply(n, num));
    let type_int = TypeOperator(TypeOperator { name : ~"Int", types : ~[]});
    let unary_func = function_type(&type_int, &type_int);
    let add_type = function_type(&type_int, &unary_func);
    env.namedTypes.insert(~"add", add_type);
    env.typecheck(&mut expr);

    let expr_type = expr.typ;
    assert!(expr_type == unary_func);
}

#[test]
fn typecheck_lambda() {
    let mut env = TypeEnvironment::new();
    let type_int = TypeOperator(TypeOperator { name : ~"Int", types : ~[]});
    let unary_func = function_type(&type_int, &type_int);
    let add_type = function_type(&type_int, &unary_func);

    let mut expr = lambda(~"x", apply(apply(identifier(~"add"), identifier(~"x")), number(1)));
    env.namedTypes.insert(~"add", add_type);
    env.typecheck(&mut expr);

    assert_eq!(expr.typ, unary_func);
}

#[test]
fn typecheck_let() {
    let mut env = TypeEnvironment::new();
    let type_int = TypeOperator(TypeOperator { name : ~"Int", types : ~[]});
    let unary_func = function_type(&type_int, &type_int);
    let add_type = function_type(&type_int, &unary_func);

    //let test x = add x in test
    let unary_bind = lambda(~"x", apply(apply(identifier(~"add"), identifier(~"x")), number(1)));
    let mut expr = let_(~[Binding { arity: 1, name: ~"test", expression: unary_bind, typeDecl: Default::default() }], identifier(~"test"));
    env.namedTypes.insert(~"add", add_type);
    env.typecheck(&mut expr);

    assert_eq!(expr.typ, unary_func);
}

#[test]
fn typecheck_case() {
    let mut env = TypeEnvironment::new();
    let type_int = TypeOperator(TypeOperator { name : ~"Int", types : ~[]});
    let unary_func = function_type(&type_int, &type_int);
    let add_type = function_type(&type_int, &unary_func);

    let mut parser = Parser::new("case [] of { : x xs -> add x 2 ; [] -> 3}".chars());
    let mut expr = parser.expression_();
    env.namedTypes.insert(~"add", add_type);
    env.typecheck(&mut expr);

    assert_eq!(expr.typ, type_int);
    match &expr.expr {
        &Case(ref case_expr, _) => {
            assert_eq!(case_expr.typ, Type::new_op(~"[]", ~[Type::new_op(~"Int", ~[])]));
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
    let bind_type0 = module.bindings[0].expression.typ;
    assert_eq!(bind_type0, typ);
}


#[test]
fn typecheck_recursive_let() {
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
        &Let(ref binds, _) => {
            assert_eq!(binds.len(), 4);
            assert_eq!(binds[0].name, ~"a");
            assert_eq!(binds[0].expression.typ, int_type);
            assert_eq!(binds[1].name, ~"test");
            assert_eq!(binds[1].expression.typ, list_type);
        }
        _ => fail!("Error")
    }
}

#[test]
fn typecheck_constraints() {
    let mut parser = Parser::new(
r"class Test a where
    test :: a -> Int

instance Test Int where
    test x = 10

main = test 1".chars());

    let mut module = parser.module();

    let mut env = TypeEnvironment::new();
    env.typecheck_module(&mut module);

    let typ = &module.bindings[0].expression.typ;
    assert_eq!(typ, &Type::new_op(~"Int", ~[]));
}

//Test that calling a function with constraints will propagate the constraints to
//the type of the caller
#[test]
fn typecheck_constraints2() {
    let mut parser = Parser::new(
r"class Test a where
    test :: a -> Int

instance Test Int where
    test x = 10

main x y = primIntAdd (test x) (test y)".chars());

    let mut module = parser.module();

    let mut env = TypeEnvironment::new();
    env.typecheck_module(&mut module);

    let typ = &module.bindings[0].expression.typ;
    let int_type = Type::new_op(~"Int", ~[]);
    let test = function_type(&Type::new_var(-1),  &function_type(&Type::new_var(-2), &int_type));
    assert_eq!(typ, &test);
    let op = typ.op();
    let test_cons = ~[~"Test"];
    assert_eq!(env.constraints.find(op.types[0].var()), Some(&test_cons));
    let second_fn = op.types[1].op();
    assert_eq!(env.constraints.find(second_fn.types[0].var()), Some(&test_cons));
}

#[test]
#[should_fail]
fn typecheck_constraints_no_instance() {
    let mut parser = Parser::new(
r"class Test a where
    test :: a -> Int

instance Test Int where
    test x = 10

main = test [1]".chars());

    let mut module = parser.module();

    let mut env = TypeEnvironment::new();
    env.typecheck_module(&mut module);
}

#[test]
fn typecheck_prelude() {
    let path = &Path::new("Prelude.hs");
    let s  = File::open(path).read_to_end();
    let contents : &str = from_utf8(s);
    let mut parser = Parser::new(contents.chars());
    let mut module = parser.module();
    let mut env = TypeEnvironment::new();
    env.typecheck_module(&mut module);

    let id = module.bindings.iter().find(|bind| bind.name == ~"id");
    assert!(id != None);
    let id_bind = id.unwrap();
    assert_eq!(id_bind.expression.typ, function_type(&Type::new_var(0), &Type::new_var(0)));
}
#[test]
fn typecheck_import() {
   
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let s  = File::open(path).read_to_end();
        let contents : &str = from_utf8(s);
        let mut parser = Parser::new(contents.chars()); 
        let mut module = parser.module();
        let mut env = TypeEnvironment::new();
        env.typecheck_module(&mut module);
        module
    };

    let mut parser = Parser::new(
r"
test1 = map not [True, False]
test2 = id (primIntAdd 2 0)".chars());
    let mut module = parser.module();

    let mut env = TypeEnvironment::new();
    env.assemblies.push(&prelude as &Types);
    env.typecheck_module(&mut module);

    assert_eq!(module.bindings[0].name, ~"test1");
    assert_eq!(module.bindings[0].expression.typ, Type::new_op(~"[]", ~[Type::new_op(~"Bool", ~[])]));
    assert_eq!(module.bindings[1].name, ~"test2");
    assert_eq!(module.bindings[1].expression.typ, Type::new_op(~"Int", ~[]));
}

#[test]
fn type_declaration() {
    
    let mut parser = Parser::new(
r"
class Test a where
    test :: a -> Int

instance Test Int where
    test x = x

test :: Test a => a -> Int -> Int
test x y = primIntAdd (test x) y".chars());
    let mut module = parser.module();

    let mut env = TypeEnvironment::new();
    env.typecheck_module(&mut module);

    assert_eq!(module.bindings[0].typeDecl.typ, module.typeDeclarations[0].typ);
}

#[test]
#[should_fail]
fn type_declaration_error() {
    
    let mut parser = Parser::new(
r"
test :: [Int] -> Int -> Int
test x y = primIntAdd x y".chars());
    let mut module = parser.module();

    let mut env = TypeEnvironment::new();
    env.typecheck_module(&mut module);
}

}
