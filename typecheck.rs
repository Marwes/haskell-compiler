use collections::HashMap;
use std::mem::swap;
use module::*;
use graph::{Graph, VertexIndex, strongly_connected_components};
use primitive::primitives;

use renamer::*;

pub use lexer::Location;
pub use module::Type;

#[cfg(test)]
use module::Alternative;

///Trait which can be implemented by types where types can be looked up by name
pub trait Types {
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Type>;
    fn find_class<'a>(&'a self, name: &str) -> Option<&'a Class>;
    fn has_instance(&self, classname: &str, typ: &Type) -> bool {
        match self.find_instance(classname, typ) {
            Some(_) => true,
            None => false
        }
    }
    fn find_instance<'a>(&'a self, classname: &str, typ: &Type) -> Option<(&'a [Constraint], &'a Type)>;
    fn each_constraint_list(&self, |&[Constraint]|);
}

pub trait DataTypes : Types {
    fn find_data_type<'a>(&'a self, name: &str) -> Option<&'a DataDefinition<Name>>;
}

//Use this to get the constructor name, ie,  extract_applied_type(Either a b) == Either
fn extract_applied_type<'a>(typ: &'a Type) -> &'a Type {
    match typ {
        &TypeApplication(ref lhs, _) => extract_applied_type(*lhs),
        _ => typ
    }
}

impl Types for Module<Name> {
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Type> {
        for bind in self.bindings.iter() {
            if bind.name == *name {
                return Some(&bind.expression.typ);
            }
        }

        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                if name.as_slice() == decl.name {
                    return Some(&decl.typ);
                }
            }
        }
        for data in self.dataDefinitions.iter() {
            for ctor in data.constructors.iter() {
                if *name == ctor.name {
                    return Some(&ctor.typ);
                }
            }
        }
        return None;
    }

    fn find_class<'a>(&'a self, name: &str) -> Option<&'a Class> {
        self.classes.iter().find(|class| name == class.name)
    }

    fn find_instance<'a>(&'a self, classname: &str, typ: &Type) -> Option<(&'a [Constraint], &'a Type)> {
        for instance in self.instances.iter() {
            if classname == instance.classname && extract_applied_type(&instance.typ) == extract_applied_type(typ) {//test name
                let c : &[Constraint] = instance.constraints;
                return Some((c, &instance.typ));
            }
        }
        None
    }

    fn each_constraint_list(&self, func: |&[Constraint]|) {
        for bind in self.bindings.iter() {
            func(bind.typeDecl.context);
        }

        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                func(decl.context);
            }
        }
    }
}

impl DataTypes for Module<Name> {
    fn find_data_type<'a>(&'a self, name: &str) -> Option<&'a DataDefinition<Name>> {
        for data in self.dataDefinitions.iter() {
            if name == extract_applied_type(&data.typ).op().name {
                return Some(data);
            }
        }
        None
    }
}

pub struct TypeEnvironment<'a> {
    assemblies: Vec<&'a DataTypes>,
    namedTypes : HashMap<Name, Type>,
    constraints: HashMap<TypeVariable, Vec<~str>>,
    instances: Vec<(~[Constraint], ~str, Type)>,
    variableIndex : int,
}

#[deriving(Clone)]
struct Substitution {
    subs: HashMap<TypeVariable, Type>,
    constraints: HashMap<TypeVariable, ~[~str]>
}

trait Bindings {
    fn get_mut<'a>(&'a mut self, idx: (uint, uint)) -> &'a mut Binding<Name>;

    fn each_binding(&self, |&Binding<Name>, (uint, uint)|);
}

impl Bindings for Module<Name> {
    fn get_mut<'a>(&'a mut self, (instance_idx, idx): (uint, uint)) -> &'a mut Binding<Name> {
        if instance_idx == 0 {
            &mut self.bindings[idx]
        }
        else {
            &mut self.instances[instance_idx - 1].bindings[idx]
        }
    }

    fn each_binding(&self, func: |&Binding<Name>, (uint, uint)|) {
        for (index, bind) in self.bindings.iter().enumerate() {
            func(bind, (0, index));
        }
        for (instance_index, instance) in self.instances.iter().enumerate() {
            for (index, bind) in instance.bindings.iter().enumerate() {
                func(bind, (instance_index + 1, index));
            }
        }
    }
}

//Woraround since traits around a vector seems problematic
struct BindingsWrapper<'a> {
    value: &'a mut [Binding<Name>]
}

impl <'a> Bindings for BindingsWrapper<'a> {
    fn get_mut<'a>(&'a mut self, (_, idx): (uint, uint)) -> &'a mut Binding<Name> {
        &mut self.value[idx]
    }

    fn each_binding(&self, func: |&Binding<Name>, (uint, uint)|) {
        for (index, bind) in self.value.iter().enumerate() {
            func(bind, (0, index));
        }
    }
}

fn insertTo(map: &mut HashMap<Name, Type>, name: ~str, typ: Type) {
    map.insert(Name { name: name, uid: 0 }, typ);
}
fn add_primitives(globals: &mut HashMap<Name, Type>, typename: &str) {
    let typ = Type::new_op(typename.to_owned(), ~[]);
    {
        let binop = function_type(&typ, &function_type(&typ, &typ));
        insertTo(globals, "prim" + typename + "Add", binop.clone());
        insertTo(globals, "prim" + typename + "Subtract", binop.clone());
        insertTo(globals, "prim" + typename + "Multiply", binop.clone());
        insertTo(globals, "prim" + typename + "Divide", binop.clone());
        insertTo(globals, "prim" + typename + "Remainder", binop.clone());
    }
    {
        let binop = function_type(&typ, &function_type(&typ, &Type::new_op(~"Bool", ~[])));
        insertTo(globals, "prim" + typename + "EQ", binop.clone());
        insertTo(globals, "prim" + typename + "LT", binop.clone());
        insertTo(globals, "prim" + typename + "LE", binop.clone());
        insertTo(globals, "prim" + typename + "GT", binop.clone());
        insertTo(globals, "prim" + typename + "GE", binop.clone());
    }
}

impl <'a> TypeEnvironment<'a> {

    ///Creates a new TypeEnvironment and adds all the primitive types
    pub fn new() -> TypeEnvironment {
        let mut globals = HashMap::new();
        add_primitives(&mut globals, &"Int");
        add_primitives(&mut globals, &"Double");
        insertTo(&mut globals, ~"primIntToDouble", function_type(&Type::new_op(~"Int", ~[]), &Type::new_op(~"Double", ~[])));
        insertTo(&mut globals, ~"primDoubleToInt", function_type(&Type::new_op(~"Double", ~[]), &Type::new_op(~"Int", ~[])));
        let var = Generic(Type::new_var_kind(-10, star_kind.clone()).var().clone());
        
        for (name, typ) in primitives().move_iter() {
            insertTo(&mut globals, name.to_owned(), typ);
        }
        let list = Type::new_op(~"[]", ~[var.clone()]);
        insertTo(&mut globals, ~"[]", list.clone());
        insertTo(&mut globals, ~":", function_type(&var, &function_type(&list, &list)));
        for i in range(0 as uint, 10) {
            let (name, typ) = tuple_type(i);
            insertTo(&mut globals, name, typ);
        }
        TypeEnvironment {
            assemblies: Vec::new(),
            namedTypes : globals,
            constraints: HashMap::new(),
            instances: Vec::new(),
            variableIndex : 0 ,
        }
    }

    pub fn add_types(&'a mut self, types: &'a DataTypes) {
        let mut max_id = 0;
        types.each_constraint_list(|context| {
            for constraint in context.iter() {
                let var = constraint.variables[0].clone();
                max_id = ::std::cmp::max(var.id, max_id);
                self.constraints.find_or_insert(var, Vec::new()).push(constraint.class.clone());
            }
        });
        self.variableIndex = max_id;
        self.assemblies.push(types);
    }

    ///Typechecks a module by updating all the types in place
    pub fn typecheck_module(&mut self, module: &mut Module<Name>) {
        for data_def in module.dataDefinitions.mut_iter() {
            let mut subs = Substitution { subs: HashMap::new(), constraints: HashMap::new() };
            freshen_all(self, &mut subs, &mut data_def.typ);
            for constructor in data_def.constructors.mut_iter() {
                replace(&mut self.constraints, &mut constructor.typ, &subs);
                let mut typ = constructor.typ.clone();
                quantify(0, &mut typ);
                self.namedTypes.insert(constructor.name.clone(), typ);
            }
        }
        for class in module.classes.mut_iter() {
            //Instantiate a new variable and replace all occurances of the class variable with this
            let mut replaced = class.variable.clone();
            let new = self.new_var();
            class.variable = new.var().clone();
            let mut var_kind = None;
            for type_decl in class.declarations.mut_iter() {
                var_kind = match find_kind(&replaced, var_kind, &type_decl.typ) {
                    Ok(k) => k,
                    Err(msg) => fail!("{}", msg)
                };
                //If we found the variable, update it immediatly since the kind of th variable
                //matters when looking for constraints, etc
                match var_kind {
                    Some(ref k) => {
                        replaced.kind.clone_from(k);
                        class.variable.kind.clone_from(k);
                        self.constraints.insert(class.variable.clone(), vec![class.name.clone()]);
                    }
                    None => ()
                }
                
                let c = Constraint { class: class.name.clone(), variables: ~[class.variable.clone()] };
                let mut mapping = HashMap::new();
                mapping.insert(replaced.clone(), TypeVariable(class.variable.clone()));
                self.freshen_declaration2(type_decl, mapping);
                {//Workaround to add the class's constraints directyly to the declaration
                    let mut context = ~[];
                    swap(&mut context, &mut type_decl.context);
                    let mut vec_context: Vec<Constraint> = context.move_iter().collect();
                    vec_context.push(c);
                    type_decl.context = vec_context.move_iter().collect();
                }
                let mut t = type_decl.typ.clone();
                quantify(0, &mut t);
                self.namedTypes.insert(Name { name: type_decl.name.clone(), uid: 0 }, t);
            }
        }
        let data_definitions = module.dataDefinitions.clone();
        for instance in module.instances.mut_iter() {
            let class = module.classes.iter().find(|class| class.name == instance.classname)
                .expect(format!("Could not find class {}", instance.classname));
            {
                let mut subs = Substitution { subs: HashMap::new(), constraints: HashMap::new() };
                for constraint in instance.constraints.mut_iter() {
                    let new = subs.subs.find_or_insert(constraint.variables[0].clone(), self.new_var_kind(constraint.variables[0].kind.clone()));
                    constraint.variables[0] = new.var().clone();
                }
                match instance.typ {
                    TypeOperator(ref mut op) => {
                        let maybe_data = self.assemblies.iter().filter_map(|a| a.find_data_type(op.name))
                            .next();
                        op.kind = maybe_data
                            .or_else(|| data_definitions.iter().find(|data| op.name == extract_applied_type(&data.typ).op().name))
                            .map(|data| extract_applied_type(&data.typ).kind().clone())
                            .unwrap_or_else(|| if "[]" == op.name { KindFunction(~StarKind, ~StarKind) } else { StarKind });
                    }
                    _ => ()
                }
                freshen_all(self, &mut subs, &mut instance.typ);
            }
            for binding in instance.bindings.mut_iter() {
                let decl = class.declarations.iter().find(|decl| binding.name.as_slice().ends_with(decl.name))
                    .expect(format!("Could not find {} in class {}", binding.name, class.name));
                binding.typeDecl = decl.clone();
                replace_var(&mut binding.typeDecl.typ, &class.variable, &instance.typ);
                {
                    let mut context = ~[];
                    swap(&mut context, &mut binding.typeDecl.context);
                    let mut vec_context: Vec<Constraint> = context.move_iter().collect();
                    for constraint in instance.constraints.iter() {
                        vec_context.push(constraint.clone());
                    }
                    binding.typeDecl.context = vec_context.move_iter().collect();
                }
                self.freshen_declaration(&mut binding.typeDecl);
                for constraint in binding.typeDecl.context.iter() {
                    self.constraints.find_or_insert(constraint.variables[0].clone(), Vec::new())
                        .push(constraint.class.clone());
                }
            }
            self.instances.push((instance.constraints.clone(), instance.classname.clone(), instance.typ.clone()));
        }
        
        for type_decl in module.typeDeclarations.mut_iter() {
            self.freshen_declaration(type_decl);

            match module.bindings.mut_iter().find(|bind| bind.name.as_slice() == type_decl.name) {
                Some(bind) => {
                    bind.typeDecl = type_decl.clone();
                }
                None => fail!("Error: Type declaration for '{}' has no binding", type_decl.name)
            }
        }

        {
            let mut subs = Substitution { subs: HashMap::new(), constraints: HashMap::new() }; 
            self.typecheck_mutually_recursive_bindings(&mut subs, module);
        }
        //FIXME
        //for bind in module.bindings.iter() {
        //    self.namedTypes.insert(bind.name.clone(), bind.expression.typ.clone());
        //}
    }

    pub fn typecheck_expr(&mut self, expr : &mut TypedExpr<Name>) {
        let mut subs = Substitution { subs: HashMap::new(), constraints: HashMap::new() }; 
        self.typecheck(expr, &mut subs);
        self.substitute(&mut subs, expr);
    }

    pub fn find(&'a self, ident: &Name) -> Option<&'a Type> {
        self.namedTypes.find(ident).or_else(|| {
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
    pub fn find_constraints(&self, typ: &Type) -> ~[Constraint] {
        let mut result : Vec<Constraint> = Vec::new();
        each_type(typ,
        |var| {
            match self.constraints.find(var) {
                Some(constraints) => {
                    for c in constraints.iter() {
                        if result.iter().find(|x| x.class == *c) == None {
                            result.push(Constraint { class: c.clone(), variables: ~[var.clone()] });
                        }
                    }
                }
                None => ()
            }
        },
        |_| ());
        result.move_iter().collect()
    }
    
    ///Searches through a type, comparing it with the type on the identifier, returning all the specialized constraints
    pub fn find_specialized_instances(&self, typ: &Type, actual_type: &Type) -> ~[(~str, Type)] {
        let mut constraints = Vec::new();
        self.find_specialized(&mut constraints, actual_type, typ);
        if constraints.len() == 0 {
            fail!("Could not find the specialized instance between {} <-> {}", typ, actual_type);
        }
        constraints.move_iter().collect()
    }
    fn find_specialized(&self, constraints: &mut Vec<(~str, Type)>, actual_type: &Type, typ: &Type) {
        match (actual_type, typ) {
            (_, &TypeVariable(ref var)) => {
                match self.constraints.find(var) {
                    Some(cons) => {
                        for c in cons.iter() {
                            if constraints.iter().find(|x| x.ref0() == c) == None {
                                constraints.push((c.clone(), actual_type.clone()));
                            }
                        }
                    }
                    None => ()
                }
            }
            (&TypeApplication(ref lhs1, ref rhs1), &TypeApplication(ref lhs2, ref rhs2)) => {
                self.find_specialized(constraints, *lhs1, *lhs2);
                self.find_specialized(constraints, *rhs1, *rhs2);
            }
            (_, &Generic(ref var)) => {
                match self.constraints.find(var) {
                    Some(cons) => {
                        for c in cons.iter() {
                            if constraints.iter().find(|x| x.ref0() == c) == None {
                                constraints.push((c.clone(), actual_type.clone()));
                            }
                        }
                    }
                    None => ()
                }
            }
            _ => ()
        }
    }

    fn freshen_declaration2(&mut self, decl: &mut TypeDeclaration, mut mapping: HashMap<TypeVariable, Type>) {
        for constraint in decl.context.mut_iter() {
            let old = constraint.variables[0].clone();
            let new = mapping.find_or_insert(old.clone(), self.new_var_kind(old.kind.clone()));
            constraint.variables[0] = new.var().clone();
        }
        let mut subs = Substitution { subs: mapping, constraints: HashMap::new() };
        freshen_all(self, &mut subs, &mut decl.typ);
    }
    fn freshen_declaration(&mut self, decl: &mut TypeDeclaration) {
        let mapping = HashMap::new();
        self.freshen_declaration2(decl, mapping);
    }

    ///Applies a substitution on all global types
    fn apply(&mut self, subs: &Substitution) {
        for (_, typ) in self.namedTypes.mut_iter() {
            replace(&mut self.constraints, typ, subs);
        }
    }

    ///Walks through an expression and applies the substitution on each of its types
    fn substitute(&mut self, subs : &Substitution, expr: &mut TypedExpr<Name>) {
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
            &Do(ref mut binds, ref mut expr) => {
                for bind in binds.mut_iter() {
                    match *bind {
                        DoExpr(ref mut expr) => self.substitute(subs, expr),
                        DoBind(_, ref mut expr) => self.substitute(subs, expr),
                        DoLet(ref mut bindings) => {
                            for bind in bindings.mut_iter() {
                                self.substitute(subs, &mut bind.expression);
                            }
                        }
                    }
                }
                self.substitute(subs, *expr);
            }
            _ => ()
        }
    }

    ///Returns whether the type 'op' has an instance for 'class'
    fn has_instance(&self, class: &str, searched_type: &Type) -> bool {
        for &(ref constraints, ref name, ref typ) in self.instances.iter() {
            if class == *name {
                if self.check_instance_constraints(*constraints, typ, searched_type) {
                    return true;
                }
            }
        }
        
        for types in self.assemblies.iter() {
            match types.find_instance(class, searched_type) {
                Some((constraints, unspecialized_type)) => {
                    return self.check_instance_constraints(constraints, unspecialized_type, searched_type);
                }
                None => ()
            }
        }
        false
    }

    fn check_instance_constraints(&self, constraints: &[Constraint], vars: &Type, types: &Type) -> bool {
        match (vars, types) {
            (&TypeApplication(ref lvar, ref rvar), &TypeApplication(ref ltype, ref rtype)) => {
                let maybeConstraint = constraints.iter().find(|c| c.variables[0] == *rvar.var());
                match maybeConstraint {
                    Some(constraint) => self.has_instance(constraint.class, *rtype)
                                     && self.check_instance_constraints(constraints, *lvar, *ltype),
                    None => false//?
                }
            }
            (&TypeOperator(ref l), &TypeOperator(ref r)) => l.name == r.name,
            (_, &TypeVariable(_)) => true,
            _ => false
        }
    }
    fn new_var_kind(&mut self, kind: Kind) -> Type {
        self.variableIndex += 1;
        Type::new_var_kind(self.variableIndex, kind)
    }

    fn new_var(&mut self) -> Type {
        self.new_var_kind(StarKind)
    }

    fn typecheck(&mut self, expr : &mut TypedExpr<Name>, subs: &mut Substitution) {
        if expr.typ == Type::new_var(0) {
            expr.typ = self.new_var();
        }

        match &mut expr.expr {
            &Number(_) => {
                self.constraints.insert(expr.typ.var().clone(), vec![~"Num"]);
                match &mut expr.typ {
                    &TypeVariable(ref mut v) => v.kind = star_kind.clone(),
                    _ => ()
                }
            }
            &Rational(_) => {
                self.constraints.insert(expr.typ.var().clone(), vec![~"Fractional"]);
                match &mut expr.typ {
                    &TypeVariable(ref mut v) => v.kind = star_kind.clone(),
                    _ => ()
                }
            }
            &String(_) => {
                expr.typ = Type::new_op(~"[]", ~[Type::new_op(~"Char", ~[])]);
            }
            &Char(_) => {
                expr.typ = Type::new_op(~"Char", ~[]);
            }
            &Identifier(ref name) => {
                match self.fresh(name) {
                    Some(t) => {
                        expr.typ = t;
                    }
                    None => fail!("Undefined identifier '{}' at {}", *name, expr.location)
                }
            }
            &Apply(ref mut func, ref mut arg) => {
                self.typecheck(*func, subs);
                replace(&mut self.constraints, &mut func.typ, subs);
                self.typecheck(*arg, subs);
                replace(&mut self.constraints, &mut arg.typ, subs);
                expr.typ = function_type(&arg.typ, &self.new_var());
                unify_location(self, subs, &expr.location, &mut func.typ, &mut expr.typ);
                expr.typ = match &expr.typ {
                    &TypeApplication(_, ref x) => (**x).clone(),
                    _ => fail!("Must be a type application (should be a function type), found {}", expr.typ)
                };
            }
            &Lambda(ref arg, ref mut body) => {
                let argType = self.new_var();
                expr.typ = function_type(&argType, &self.new_var());

                {
                    self.namedTypes.insert(arg.clone(), argType.clone());
                    self.typecheck(*body, subs);
                }
                replace(&mut self.constraints, &mut expr.typ, subs);
                with_arg_return(&mut expr.typ, |_, return_type| {
                    *return_type = body.typ.clone();
                });
            }
            &Let(ref mut bindings, ref mut body) => {

                {
                    self.typecheck_mutually_recursive_bindings(subs, &mut BindingsWrapper { value: *bindings });
                    self.apply(subs);
                    self.typecheck(*body, subs);
                }

                replace(&mut self.constraints, &mut body.typ, subs);
                expr.typ = body.typ.clone();
            }
            &Case(ref mut case_expr, ref mut alts) => {
                self.typecheck(*case_expr, subs);
                self.typecheck_pattern(&alts[0].pattern.location, subs, &alts[0].pattern.node, &mut case_expr.typ);
                self.typecheck(&mut alts[0].expression, subs);
                let mut alt0_ = alts[0].expression.typ.clone();
                for alt in alts.mut_iter().skip(1) {
                    self.typecheck_pattern(&alt.pattern.location, subs, &alt.pattern.node, &mut case_expr.typ);
                    self.typecheck(&mut alt.expression, subs);
                    unify_location(self, subs, &alt.expression.location, &mut alt0_, &mut alt.expression.typ);
                    replace(&mut self.constraints, &mut alt.expression.typ, subs);
                }
                replace(&mut self.constraints, &mut alts[0].expression.typ, subs);
                replace(&mut self.constraints, &mut case_expr.typ, subs);
                expr.typ = alt0_;
            }
            &Do(ref mut bindings, ref mut last_expr) => {
                let mut previous = self.new_var_kind(KindFunction(~StarKind, ~StarKind));
                self.constraints.insert(previous.var().clone(), vec!(~"Monad"));
                previous = TypeApplication(~previous, ~self.new_var());
                for bind in bindings.mut_iter() {
                    match *bind {
                        DoExpr(ref mut e) => {
                            self.typecheck(e, subs);
                            unify_location(self, subs, &e.location, &mut e.typ, &mut previous);
                        }
                        DoLet(ref mut bindings) => {
                            self.typecheck_mutually_recursive_bindings(subs, &mut BindingsWrapper { value: *bindings });
                            self.apply(subs);
                        }
                        DoBind(ref mut pattern, ref mut e) => {
                            self.typecheck(e, subs);
                            unify_location(self, subs, &e.location, &mut e.typ, &mut previous);
                            let inner_type = match e.typ {
                                TypeApplication(_, ref mut t) => t,
                                _ => fail!("Not a monadic type: {}", e.typ)
                            };
                            self.typecheck_pattern(&pattern.location, subs, &pattern.node, *inner_type);
                        }
                    }
                    match previous {
                        TypeApplication(ref mut _monad, ref mut typ) => {
                            **typ = self.new_var();
                        }
                        _ => fail!()
                    }
                }
                self.typecheck(*last_expr, subs);
                unify_location(self, subs, &last_expr.location, &mut last_expr.typ, &mut previous);
                expr.typ.clone_from(&last_expr.typ);
            }
        };
    }

    fn typecheck_pattern(&mut self, location: &Location, subs: &mut Substitution, pattern: &Pattern<Name>, match_type: &mut Type) {
        match pattern {
            &IdentifierPattern(ref ident) => {
                let mut typ = self.new_var();
                {
                    unify_location(self, subs, location, &mut typ, match_type);
                    replace(&mut self.constraints, match_type, subs);
                    replace(&mut self.constraints, &mut typ, subs);
                }
                self.namedTypes.insert(ident.clone(), typ.clone());
            }
            &NumberPattern(_) => {
                let mut typ = Type::new_op(~"Int", ~[]);
                {
                    unify_location(self, subs, location, &mut typ, match_type);
                    replace(&mut self.constraints, match_type, subs);
                    replace(&mut self.constraints, &mut typ, subs);
                }
            }
            &ConstructorPattern(ref ctorname, ref patterns) => {
                let mut t = self.fresh(ctorname).expect(format!("Undefined constructer '{}' when matching pattern", *ctorname));
                let mut data_type = get_returntype(&t);
                
                unify_location(self, subs, location, &mut data_type, match_type);
                replace(&mut self.constraints, match_type, subs);
                replace(&mut self.constraints, &mut t, subs);
                self.apply(subs);
                self.pattern_rec(0, location, subs, *patterns, &mut t);
            }
            &WildCardPattern => {
                fail!("Wildcard pattern not implemented in typechecking")
            }
        }
    }

    fn pattern_rec(&mut self, i: uint, location: &Location, subs: &mut Substitution, patterns: &[Pattern<Name>], func_type: &mut Type) {
        if i < patterns.len() {
            let p = &patterns[i];
            with_arg_return(func_type, |arg_type, return_type| {
                self.typecheck_pattern(location, subs, p, arg_type);
                self.pattern_rec(i + 1, location, subs, patterns, return_type);
            });
        }
    }

    pub fn typecheck_mutually_recursive_bindings(&mut self, subs: &mut Substitution, bindings: &mut Bindings) {
        let start_var_index = self.variableIndex + 1;
        
        let graph = build_graph(bindings);
        let groups = strongly_connected_components(&graph);

        for i in range(0, groups.len()) {
            let group = &groups[i];
            for index in group.iter() {
                let bindIndex = graph.get_vertex(*index).value;
                let bind = bindings.get_mut(bindIndex);
                bind.expression.typ = self.new_var();
                self.namedTypes.insert(bind.name.clone(), bind.expression.typ.clone());
                if bind.typeDecl.typ == Type::new_var(0) {
                    bind.typeDecl.typ = self.new_var();
                }
            }
            
            for index in group.iter() {
                {
                    let bindIndex = graph.get_vertex(*index).value;
                    let bind = bindings.get_mut(bindIndex);
                    debug!("Begin typecheck {} :: {}", bind.name, bind.expression.typ);
                    let type_var = bind.expression.typ.var().clone();
                    self.typecheck(&mut bind.expression, subs);
                    unify_location(self, subs, &bind.expression.location, &mut bind.typeDecl.typ, &mut bind.expression.typ);
                    self.substitute(subs, &mut bind.expression);
                    subs.subs.insert(type_var, bind.expression.typ.clone());
                    self.apply(subs);
                    debug!("End typecheck {} :: {}", bind.name, bind.expression.typ);
                }
            }
            
            for index in group.iter() {
                let bindIndex = graph.get_vertex(*index).value;
                let bind = bindings.get_mut(bindIndex);
                self.substitute(subs, &mut bind.expression);
                bind.typeDecl.typ = bind.expression.typ.clone();
                bind.typeDecl.context = self.find_constraints(&bind.typeDecl.typ);
                let typ = self.namedTypes.get_mut(&bind.name);
                quantify(start_var_index, typ);
            }
        }
    }

    ///Instantiates new typevariables for every typevariable in the type found at 'name'
    fn fresh(&'a mut self, name: &Name) -> Option<Type> {
        match self.find(name).map(|x| x.clone()) {
            Some(mut typ) => {
                let mut subs = Substitution { subs: HashMap::new(), constraints: HashMap::new() };
                freshen(self, &mut subs, &mut typ);
                Some(typ)
            }
            None => None
        }
    }

}

fn quantify(start_var_index: int, typ: &mut Type) {
    let x = match typ {
        &TypeVariable(ref id) if id.id > start_var_index => Some(id.clone()),
        &TypeApplication(ref mut lhs, ref mut rhs) => {
            quantify(start_var_index, *lhs);
            quantify(start_var_index, *rhs);
            None
        }
        _ => None
    };
    match x {
        Some(var) => *typ = Generic(var),
        None => ()
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
        &TypeOperator(_) => None,
        &TypeApplication(ref mut lhs, ref mut rhs) => {
            replace_var(*lhs, var, replacement);
            replace_var(*rhs, var, replacement);
            None
        }
        &Generic(_) => fail!("replace_var called on Generic")
    };
    match new {
        Some(x) => {
            *typ = x.clone();
        }
        None => ()
    }
}

fn is_function(typ: &Type) -> bool {
    match typ {
        &TypeApplication(ref lhs, _) => {
            let l: &Type = *lhs;
            match l  {
                &TypeApplication(ref lhs, _) => {
                    let l: &Type = *lhs;
                    match l {
                        &TypeOperator(ref op) => op.name.equiv(& &"->"),
                        _ => false
                    }
                }
                _ => false
            }
        }
        _ => false
    }
}

fn get_returntype(typ: &Type) -> Type {
    match typ {
        &TypeApplication(_, ref rhs) => {
            if is_function(typ) {
                get_returntype(*rhs)
            }
            else {
                typ.clone()
            }
        }
        _ => typ.clone()
    }
}

///Update the constraints when replacing the variable 'old' with 'new'
fn update_constraints(constraints: &mut HashMap<TypeVariable, Vec<~str>>, old: &TypeVariable, new: &Type, subs: &Substitution) {
    match new {
        &TypeVariable(ref new_var) => {
            match subs.constraints.find(old) {
                Some(subs_constraints) => {
                    let to_update = constraints.find_or_insert(new_var.clone(), Vec::new());
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
fn replace(constraints: &mut HashMap<TypeVariable, Vec<~str>>, old : &mut Type, subs : &Substitution) {
    let replaced = match old {
        &TypeVariable(ref id) => {
            match subs.subs.find(id) {
                Some(new) => {
                    update_constraints(constraints, id, new, subs);
                    Some(new.clone())
                }
                None => None
            }
        }
        &TypeOperator(_) => None,
        &TypeApplication(ref mut lhs, ref mut rhs) => {
            replace(constraints, *lhs, subs);
            replace(constraints, *rhs, subs);
            None
        }
        &Generic(_) => None, //fail!("replace called on Generic")
    };
    match replaced {
        Some(x) => {
            let is_var = match old {
                &TypeVariable(_) => true,
                _ => false
            };
            if is_var {
                *old = x;
            }
            else {
                *old = x;
            }
        }
        None => ()
    }
}

///Checks whether a typevariable occurs in another type
fn occurs(type_var: &TypeVariable, inType: &Type) -> bool {
    match inType {
        &TypeVariable(ref var) => type_var.id == var.id,
        &TypeApplication(ref lhs, ref rhs) => occurs(type_var, *lhs) || occurs(type_var, *rhs),
        _ => false
    }
}

fn freshen(env: &mut TypeEnvironment, subs: &mut Substitution, typ: &mut Type) {
    let result = match typ {
        &Generic(ref id) => {
            let new = env.new_var_kind(id.kind.clone());
            let maybe_constraints = match env.constraints.find(id) {
                Some(constraints) => Some(constraints.clone()),
                None => None
            };
            match (maybe_constraints, new.clone()) {
                (Some(c), TypeVariable(newid)) => {
                    env.constraints.insert(newid, c);
                }
                _ => ()
            }
            Some(subs.subs.find_or_insert(id.clone(), new.clone()).clone())
        }
        &TypeApplication(ref mut lhs, ref mut rhs) => {
            freshen(env, subs, *lhs);
            freshen(env, subs, *rhs);
            None
        }
        _ => None
    };
    match result {
        Some(x) => *typ = x,
        None => ()
    }
}
fn freshen_all(env: &mut TypeEnvironment, subs: &mut Substitution, typ: &mut Type) {
    let result = match typ {
        &TypeVariable(ref id) => {
            let t = match subs.subs.find(id) {
                Some(var) => Some(var.clone()),
                _ => {
                    None
                }
            };
            if t.is_some() {
                t
            }
            else {
                let new = env.new_var_kind(id.kind.clone());
                let maybe_constraints = match env.constraints.find(id) {
                    Some(constraints) => Some(constraints.clone()),
                    None => None
                };
                match (maybe_constraints, new.clone()) {
                    (Some(c), TypeVariable(newid)) => {
                        env.constraints.insert(newid, c);
                    }
                    _ => ()
                }
                Some(subs.subs.find_or_insert(id.clone(), new.clone()).clone())
            }
        }
        &TypeApplication(ref mut lhs, ref mut rhs) => {
            freshen_all(env, subs, *lhs);
            freshen_all(env, subs, *rhs);
            None
        }
        _ => None
    };
    match result {
        Some(mut x) => {
            let k = x.kind().clone();
            match x {
                TypeVariable(ref mut v) => v.kind = k,
                _ => ()
            }
            *typ = x;
        }
        None => ()
    }
}

///Takes two types and attempts to make them the same type
fn unify_location(env: &mut TypeEnvironment, subs: &mut Substitution, location: &Location, lhs: &mut Type, rhs: &mut Type) {
    debug!("Unifying {} <-> {}", *lhs, *rhs);
    match unify(env, subs, lhs.clone(), rhs.clone()) {
        Ok(typ) => {
            let subs2 = subs.clone();
            for (_, ref mut typ) in subs.subs.mut_iter() {
                replace(&mut env.constraints, *typ, &subs2);
            }
            *lhs = typ.clone();
            *rhs = typ;
        }
        Err(error) => match error {
            UnifyFail => fail!("{} Error: Could not unify types {}\nand\n{}", location, *lhs, *rhs),
            RecursiveUnification => fail!("{} Error: Recursive unification between {}\nand\n{}", location, *lhs, *rhs),
            WrongArity(l, r) =>
                fail!("{} Error: Types do not have the same arity.\n{} <-> {}\n{} <-> {}\n{}\nand\n{}"
                    , location, l, r, l.kind(), r.kind(), *lhs, *rhs),
            MissingInstance(class, typ, id) => fail!("{} Error: The instance {} {} was not found as required by {} when unifying {}\nand\n{}", location, class, typ, id, *lhs, *rhs)
        }
    }
    debug!("Unify end");
}

enum TypeError {
    UnifyFail,
    RecursiveUnification,
    WrongArity(Type, Type),
    MissingInstance(~str, Type, TypeVariable)
}

fn unify(env: &mut TypeEnvironment, subs: &mut Substitution, lhs: Type, rhs: Type) -> Result<Type, TypeError> {
    fn bind_variable(env: &mut TypeEnvironment, subs: &mut Substitution, var: TypeVariable, typ: Type) -> Result<Type, TypeError> {
        let x = match &typ {
            &TypeVariable(ref var2) => {
                if var != *var2 {
                    subs.subs.insert(var.clone(), typ.clone());
                    match env.constraints.pop(&var) {
                        Some(constraints) => {
                            let to_update = env.constraints.find_or_insert(var2.clone(), Vec::new());
                            for c in constraints.iter() {
                                if to_update.iter().find(|x| *x == c) == None {
                                    to_update.push(c.clone());
                                }
                            }
                        }
                        None => ()
                    }
                }
                Ok(())
            }
            _ => {
                if occurs(&var, &typ) {
                    return Err(RecursiveUnification);
                }
                else if var.kind != *typ.kind() && var.kind != star_kind {
                    return Err(WrongArity(TypeVariable(var.clone()), typ.clone()));
                }
                else {
                    for (_, replaced) in subs.subs.mut_iter() {
                        replace_var(replaced, &var, &typ);
                    }
                    subs.subs.insert(var.clone(), typ.clone());
                    match env.constraints.find(&var) {
                        Some(constraints) => {
                            for c in constraints.iter() {
                                if !env.has_instance(*c, &typ) {
                                    match &typ {
                                        &TypeOperator(ref op) => {
                                            if c.equiv(& &"Num") && (op.name.equiv(& &"Int") || op.name.equiv(& &"Double")) && *typ.kind() == star_kind {
                                                continue;
                                            }
                                            else if c.equiv(& &"Fractional") && "Double" == op.name && *typ.kind() == star_kind {
                                                continue;
                                            }
                                        }
                                        _ => ()
                                    }
                                    return Err(MissingInstance(c.clone(), typ.clone(), var));
                                }
                            }
                        }
                        _ => ()
                    }
                    Ok(())
                }
            }
        };
        match x {
            Ok(_) => Ok(typ),
            Err(e) => Err(e)
        }
    }
    match (lhs, rhs) {
        (TypeApplication(l1, mut r1), TypeApplication(l2, mut r2)) => {
            match unify(env, subs, *l1, *l2) {
                Ok(arg) => {
                    replace(&mut env.constraints, r1, subs);
                    replace(&mut env.constraints, r2, subs);
                    match unify(env, subs, *r1, *r2) {
                        Ok(typ) => Ok(TypeApplication(~arg, ~typ)),
                        Err(e) => Err(e)
                    }
                }
                Err(e) => Err(e)
            }
        }
        (TypeVariable(lhs), TypeVariable(rhs)) => {
            //If both are variables we choose that they younger variable is replaced by the oldest
            //This is because when doing the quantifying, only variables that are created during
            //the inference of mutually recursive bindings should be quantified, but if a newly
            //created variable is unified with one from an outer scope we need to prefer the older
            //so that the variable does not get quantified
            if lhs.id > rhs.id {
                bind_variable(env, subs, lhs, TypeVariable(rhs))
            }
            else {
                bind_variable(env, subs, rhs, TypeVariable(lhs))
            }
        }
        (TypeVariable(var), rhs) => { bind_variable(env, subs, var, rhs) }
        (lhs, TypeVariable(var)) => { bind_variable(env, subs, var, lhs) }
        (TypeOperator(lhs), TypeOperator(rhs)) =>
            if lhs.name == rhs.name { Ok(TypeOperator(lhs)) } else { Err(UnifyFail) },
        _ => Err(UnifyFail)
    }
}

///Creates a graph containing a vertex for each binding and edges for each 
fn build_graph(bindings: &Bindings) -> Graph<(uint, uint)> {
    let mut graph = Graph::new();
    let mut map = HashMap::new();
    bindings.each_binding(|bind, i| {
        let index = graph.new_vertex(i);
        map.insert(bind.name.clone(), index);
    });
    bindings.each_binding(|bind, _| {
        add_edges(&mut graph, &map, *map.get(&bind.name), &bind.expression);
    });
    graph
}

fn add_edges<T>(graph: &mut Graph<T>, map: &HashMap<Name, VertexIndex>, function_index: VertexIndex, expr: &TypedExpr<Name>) {
    match &expr.expr {
        &Identifier(ref n) => {
            match map.find(n) {
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
        &TypeOperator(ref op) => (*op_fn)(op),
        &TypeApplication(ref lhs, ref rhs) => {
            each_type_(*lhs, var_fn, op_fn);
            each_type_(*rhs, var_fn, op_fn);
        }
        _ => ()
    }
}

///Finds the kind for the variable test and makes sure that all occurences of the variable
///has the same kind in 'typ'
///'expected' should be None if the kinds is currently unknown, otherwise the expected kind
fn find_kind(test: &TypeVariable, expected: Option<Kind>, typ: &Type) -> Result<Option<Kind>, ~str> {
    match *typ {
        TypeVariable(ref var) if test.id == var.id => {
            match expected {
                Some(k) => {
                    if k != var.kind {
                        Err("Kinds do not match".to_owned())
                    }
                    else {
                        Ok(Some(k))
                    }
                }
                None => Ok(Some(var.kind.clone()))
            }
        }
        TypeApplication(ref lhs, ref rhs) => {
            find_kind(test, expected, *lhs)
                .and_then(|result| {
                    find_kind(test, result, *rhs)
                })
        }
        _ => Ok(expected)
    }
}

pub fn function_type(func : &Type, arg : &Type) -> Type {
    Type::new_op(~"->", ~[func.clone(), arg.clone()])
}

pub fn function_type_(func : Type, arg : Type) -> Type {
    Type::new_op(~"->", ~[func, arg])
}

pub fn with_arg_return(func_type: &mut Type, func: |&mut Type, &mut Type|) -> bool {
    match func_type {
        &TypeApplication(ref mut lhs, ref mut return_type) => {
            let l: &mut Type = *lhs;
            match l {
                &TypeApplication(_, ref mut arg_type) => {
                    func(*arg_type, *return_type);
                    true
                }
                _ => false
            }
        }
        _ => false
    }
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
use renamer::*;

use parser::Parser;
use std::io::File;

use test::Bencher;

#[test]
fn application() {
    let mut env = TypeEnvironment::new();
    let n = ~TypedExpr::new(Identifier(~"primIntAdd"));
    let num = ~TypedExpr::new(Number(1));
    let e = TypedExpr::new(Apply(n, num));
    let mut expr = rename_expr(e);
    let type_int = Type::new_op(~"Int", ~[]);
    let unary_func = function_type(&type_int, &type_int);
    env.typecheck_expr(&mut expr);

    let expr_type = expr.typ;
    assert!(expr_type == unary_func);
}

#[test]
fn typecheck_lambda() {
    let mut env = TypeEnvironment::new();
    let type_int = Type::new_op(~"Int",~[]);
    let unary_func = function_type(&type_int, &type_int);

    let e = lambda(~"x", apply(apply(identifier(~"primIntAdd"), identifier(~"x")), number(1)));
    let mut expr = rename_expr(e);
    env.typecheck_expr(&mut expr);

    assert_eq!(expr.typ, unary_func);
}

#[test]
fn typecheck_let() {
    let mut env = TypeEnvironment::new();
    let type_int = Type::new_op(~"Int", ~[]);
    let unary_func = function_type(&type_int, &type_int);

    //let test x = add x in test
    let unary_bind = lambda(~"x", apply(apply(identifier(~"primIntAdd"), identifier(~"x")), number(1)));
    let e = let_(~[Binding { arity: 1, name: ~"test", expression: unary_bind, typeDecl: Default::default() }], identifier(~"test"));
    let mut expr = rename_expr(e);
    env.typecheck_expr(&mut expr);

    assert_eq!(expr.typ, unary_func);
}

#[test]
fn typecheck_case() {
    let mut env = TypeEnvironment::new();
    let type_int = Type::new_op(~"Int", ~[]);

    let mut parser = Parser::new(r"case [] of { : x xs -> primIntAdd x 2 ; [] -> 3}".chars());
    let mut expr = rename_expr(parser.expression_());
    env.typecheck_expr(&mut expr);

    assert_eq!(expr.typ, type_int);
    match &expr.expr {
        &Case(ref case_expr, _) => {
            assert_eq!(case_expr.typ, Type::new_op(~"[]", ~[Type::new_op(~"Int", ~[])]));
        }
        _ => fail!("typecheck_case")
    }
}

#[test]
fn typecheck_list() {
    let file =
r"mult2 x = primIntMultiply x 2

main = case [mult2 123, 0] of
    : x xs -> x
    [] -> 10";
    let module = do_typecheck(file);

    assert_eq!(module.bindings[1].expression.typ, Type::new_op(~"Int", ~[]));
}

#[test]
fn typecheck_string() {
    let mut env = TypeEnvironment::new();

    let mut parser = Parser::new("\"hello\"".chars());
    let mut expr = rename_expr(parser.expression_());
    env.typecheck_expr(&mut expr);

    assert_eq!(expr.typ, Type::new_op(~"[]", ~[Type::new_op(~"Char", ~[])]));
}

#[test]
fn typecheck_tuple() {
    let mut env = TypeEnvironment::new();

    let mut parser = Parser::new("(primIntAdd 0 0, \"a\")".chars());
    let mut expr = rename_expr(parser.expression_());
    env.typecheck_expr(&mut expr);

    let list = Type::new_op(~"[]", ~[Type::new_op(~"Char", ~[])]);
    assert_eq!(expr.typ, Type::new_op(~"(,)", ~[Type::new_op(~"Int", ~[]), list]));
}

#[test]
fn typecheck_module() {

    let file =
r"data Bool = True | False
test x = True";
    let module = do_typecheck(file);

    let typ = function_type(&Type::new_var(0), &Type::new_op(~"Bool", ~[]));
    let bind_type0 = module.bindings[0].expression.typ;
    assert_eq!(bind_type0, typ);
}


#[test]
fn typecheck_recursive_let() {
    let mut env = TypeEnvironment::new();

    let mut parser = Parser::new(
r"let
    a = primIntAdd 0 1
    test = primIntAdd 1 2 : test2
    test2 = 2 : test
    b = test
in b".chars());
    let mut expr = rename_expr(parser.expression_());
    env.typecheck_expr(&mut expr);

    
    let int_type = Type::new_op(~"Int", ~[]);
    let list_type = Type::new_op(~"[]", ~[int_type.clone()]);
    match &expr.expr {
        &Let(ref binds, _) => {
            assert_eq!(binds.len(), 4);
            assert_eq!(binds[0].name.as_slice(), "a");
            assert_eq!(binds[0].expression.typ, int_type);
            assert_eq!(binds[1].name.as_slice(), "test");
            assert_eq!(binds[1].expression.typ, list_type);
        }
        _ => fail!("Error")
    }
}

#[test]
fn typecheck_constraints() {
    let file =
r"class Test a where
    test :: a -> Int

instance Test Int where
    test x = 10

main = test 1";

    let module = do_typecheck(file);

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

    let mut module = rename_module(parser.module());

    let mut env = TypeEnvironment::new();
    env.typecheck_module(&mut module);

    let typ = &module.bindings[0].expression.typ;
    let int_type = Type::new_op(~"Int", ~[]);
    let test = function_type(&Type::new_var(-1),  &function_type(&Type::new_var(-2), &int_type));
    assert_eq!(typ, &test);
    let test_cons = vec![~"Test"];
    assert_eq!(env.constraints.find(typ.appl().appr().var()), Some(&test_cons));
    let second_fn = &typ.appr();
    assert_eq!(env.constraints.find(second_fn.appl().appr().var()), Some(&test_cons));
}

#[test]
#[should_fail]
fn typecheck_constraints_no_instance() {
    let file =
r"class Test a where
    test :: a -> Int

instance Test Int where
    test x = 10

main = test [1]";

    do_typecheck(file);
}

#[test]
fn typecheck_instance_super_class() {
    let mut parser = Parser::new(
r"data Bool = True | False

class Eq a where
    (==) :: a -> a -> Bool

instance Eq a => Eq [a] where
    (==) xs ys = case xs of
        : x2 xs2 -> case ys of
            : y2 ys2 -> (x2 == y2) && (xs2 == ys2)
            [] -> False
        [] -> case ys of
            : y2 ys2 -> False
            [] -> True

(&&) :: Bool -> Bool -> Bool
(&&) x y = case x of
    True -> y
    False -> False
".chars());

    let mut module = rename_module(parser.module());

    let mut env = TypeEnvironment::new();
    env.typecheck_module(&mut module);

    let typ = &module.instances[0].bindings[0].expression.typ;
    let list_type = Type::new_op(~"[]", ~[Type::new_var(100)]);
    assert_eq!(*typ, function_type(&list_type, &function_type(&list_type, &Type::new_op(~"Bool", ~[]))));
    let var = typ.appl().appr().appr().var();
    let eq = vec![~"Eq"];
    assert_eq!(env.constraints.find(var), Some(&eq));
}

#[test]
fn typecheck_num_double() {

    let file = 
r"test x = primDoubleAdd 0 x";
    let module = do_typecheck(file);

    let typ = function_type(&Type::new_op(~"Double", ~[]), &Type::new_op(~"Double", ~[]));
    let bind_type0 = module.bindings[0].expression.typ;
    assert_eq!(bind_type0, typ);
}

#[test]
fn typecheck_functor() {
    let file = 
r"data Maybe a = Just a | Nothing

class Functor f where
    fmap :: (a -> b) -> f a -> f b

instance Functor Maybe where
    fmap f x = case x of
        Just y -> Just (f y)
        Nothing -> Nothing

add2 x = primIntAdd x 2
main = fmap add2 (Just 3)";
    let module = do_typecheck(file);

    let main = &module.bindings[1];
    assert_eq!(main.expression.typ, Type::new_op(~"Maybe", ~[Type::new_op(~"Int", ~[])]));
}
#[should_fail]
#[test]
fn typecheck_functor_error() {

    do_typecheck(
r"data Maybe a = Just a | Nothing

class Functor f where
    fmap :: (a -> b) -> f a -> f b

instance Functor Maybe where
    fmap f x = case x of
        Just y -> Just (f y)
        Nothing -> Nothing

add2 x = primIntAdd x 2
main = fmap add2 3");
}

#[test]
fn typecheck_prelude() {
    let path = &Path::new("Prelude.hs");
    let contents = File::open(path).read_to_str().unwrap();
    let module = do_typecheck(contents);

    let id = module.bindings.iter().find(|bind| bind.name.as_slice() == "id");
    assert!(id != None);
    let id_bind = id.unwrap();
    assert_eq!(id_bind.expression.typ, function_type(&Type::new_var(0), &Type::new_var(0)));
}

#[test]
fn typecheck_import() {
   
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let contents = File::open(path).read_to_str().unwrap();
        do_typecheck(contents)
    };

    let file = 
r"
test1 = map not [True, False]
test2 = id (primIntAdd 2 0)";
    let module = do_typecheck_with(file, [&prelude as &DataTypes]);

    assert_eq!(module.bindings[0].name.as_slice(), "test1");
    assert_eq!(module.bindings[0].expression.typ, Type::new_op(~"[]", ~[Type::new_op(~"Bool", ~[])]));
    assert_eq!(module.bindings[1].name.as_slice(), "test2");
    assert_eq!(module.bindings[1].expression.typ, Type::new_op(~"Int", ~[]));
}

#[test]
fn type_declaration() {
    
    let input =
r"
class Test a where
    test :: a -> Int

instance Test Int where
    test x = x

test :: Test a => a -> Int -> Int
test x y = primIntAdd (test x) y";
    let module = do_typecheck(input);

    assert_eq!(module.bindings[0].typeDecl.typ, module.typeDeclarations[0].typ);
}

#[test]
fn do_expr_simple() {
    
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let contents = File::open(path).read_to_str().unwrap();
        do_typecheck(contents)
    };

    let file = 
r"
test x = do
    let y = reverse x
    putStrLn y
";
    let module = do_typecheck_with(file, [&prelude as &DataTypes]);

    assert_eq!(module.bindings[0].expression.typ, function_type_(list_type(char_type()), io(unit())));
}

#[test]
fn do_expr_pattern() {
    
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let contents = File::open(path).read_to_str().unwrap();
        do_typecheck(contents)
    };

    let file = 
r"
test x = do
    : y ys <- x
    return y
";
    let module = do_typecheck_with(file, [&prelude as &DataTypes]);

    let var = Type::new_var(0);
    let t = function_type_(Type::new_var_args(2, ~[list_type(var.clone())]), Type::new_var_args(2, ~[var.clone()]));
    assert_eq!(module.bindings[0].expression.typ, t);
    assert_eq!(module.bindings[0].typeDecl.context[0].class.as_slice(), "Monad");
}
#[test]
#[should_fail]
fn do_expr_wrong_monad() {
    
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let contents = File::open(path).read_to_str().unwrap();
        do_typecheck(contents)
    };

    let file = 
r"
test x = do
    putStrLn x
    reverse [primIntAdd 0 0, 1, 2]";
    do_typecheck_with(file, [&prelude as &DataTypes]);
}



fn do_typecheck(input: &str) -> Module<Name> {
    do_typecheck_with(input, [])
}
fn do_typecheck_with(input: &str, types: &[&DataTypes]) -> Module<Name> {
    let mut parser = Parser::new(input.chars());
    let mut module = rename_module(parser.module());
    let mut env = TypeEnvironment::new();
    for t in types.iter() {
        env.add_types(*t);
    }
    env.typecheck_module(&mut module);
    module
}

#[test]
#[should_fail]
fn wrong_type() {
    do_typecheck(r"test = primIntAdd 2 []");
}

#[test]
#[should_fail]
fn argument_count_error() {
    do_typecheck("test = primIntAdd 2 2 3");
}
#[test]
#[should_fail]
fn case_alternative_error() {
    do_typecheck(
r"
test = case [primIntAdd 1 2] of
    [] -> primIntAdd 0 1
    2 -> 1");
}

#[test]
#[should_fail]
fn type_declaration_error() {
    do_typecheck(
r"
test :: [Int] -> Int -> Int
test x y = primIntAdd x y");
}

#[bench]
fn bench_prelude(b: &mut Bencher) {
    let path = &Path::new("Prelude.hs");
    let contents = File::open(path).read_to_str().unwrap();
    let mut parser = Parser::new(contents.chars());
    let module = rename_module(parser.module());

    b.iter(|| {
        let mut env = TypeEnvironment::new();
        let mut m = module.clone();
        env.typecheck_module(&mut m);
    });
}

}
