use collections::HashMap;
use std::mem::swap;
use std::vec::FromVec;
use std::io::IoResult;
use module::*;
use graph::{Graph, VertexIndex, strongly_connected_components};
use primitive::primitives;
use renamer::*;
use interner::*;

pub use lexer::Location;
pub use module::Type;

#[cfg(test)]
use module::Alternative;

///Trait which can be implemented by types where types can be looked up by name
pub trait Types {
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Type>;
    fn find_class<'a>(&'a self, name: InternedStr) -> Option<&'a Class>;
    fn has_instance(&self, classname: InternedStr, typ: &Type) -> bool {
        match self.find_instance(classname, typ) {
            Some(_) => true,
            None => false
        }
    }
    fn find_instance<'a>(&'a self, classname: InternedStr, typ: &Type) -> Option<(&'a [Constraint], &'a Type)>;
    fn each_constraint_list(&self, |&[Constraint]|);
}

pub trait DataTypes : Types {
    fn find_data_type<'a>(&'a self, name: InternedStr) -> Option<&'a DataDefinition<Name>>;
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
                if name.name == decl.name {
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

    fn find_class<'a>(&'a self, name: InternedStr) -> Option<&'a Class> {
        self.classes.iter().find(|class| name == class.name)
    }

    fn find_instance<'a>(&'a self, classname: InternedStr, typ: &Type) -> Option<(&'a [Constraint], &'a Type)> {
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
    fn find_data_type<'a>(&'a self, name: InternedStr) -> Option<&'a DataDefinition<Name>> {
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
    local_types : HashMap<Name, Type>,
    constraints: HashMap<TypeVariable, Vec<InternedStr>>,
    instances: Vec<(~[Constraint], InternedStr, Type)>,
    variableIndex : int,
}

#[deriving(Clone)]
struct Substitution {
    subs: HashMap<TypeVariable, Type>,
    constraints: HashMap<TypeVariable, ~[InternedStr]>
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

fn insertTo(map: &mut HashMap<Name, Type>, name: &str, typ: Type) {
    map.insert(Name { name: intern(name), uid: 0 }, typ);
}
fn prim(typename: &str, op: &str) -> StrBuf {
    let mut b = StrBuf::from_str("prim");
    b.push_str(typename);
    b.push_str(op);
    b
}
fn add_primitives(globals: &mut HashMap<Name, Type>, typename: &str) {
    let typ = Type::new_op(intern(typename), ~[]);
    {
        let binop = function_type(&typ, &function_type(&typ, &typ));
        insertTo(globals, prim(typename, "Add").as_slice(), binop.clone());
        insertTo(globals, prim(typename, "Subtract").as_slice(), binop.clone());
        insertTo(globals, prim(typename, "Multiply").as_slice(), binop.clone());
        insertTo(globals, prim(typename, "Divide").as_slice(), binop.clone());
        insertTo(globals, prim(typename, "Remainder").as_slice(), binop.clone());
    }
    {
        let binop = function_type_(typ.clone(), function_type_(typ, bool_type()));
        insertTo(globals, prim(typename, "EQ").as_slice(), binop.clone());
        insertTo(globals, prim(typename, "LT").as_slice(), binop.clone());
        insertTo(globals, prim(typename, "LE").as_slice(), binop.clone());
        insertTo(globals, prim(typename, "GT").as_slice(), binop.clone());
        insertTo(globals, prim(typename, "GE").as_slice(), binop.clone());
    }
}

impl <'a> TypeEnvironment<'a> {

    ///Creates a new TypeEnvironment and adds all the primitive types
    pub fn new() -> TypeEnvironment {
        let mut globals = HashMap::new();
        add_primitives(&mut globals, "Int");
        add_primitives(&mut globals, "Double");
        insertTo(&mut globals,"primIntToDouble", function_type_(int_type(), double_type()));
        insertTo(&mut globals, "primDoubleToInt", function_type_(double_type(), int_type()));
        let var = Generic(Type::new_var_kind(-10, star_kind.clone()).var().clone());
        
        for (name, typ) in primitives().move_iter() {
            insertTo(&mut globals, name, typ);
        }
        let list = list_type(var.clone());
        insertTo(&mut globals, "[]", list.clone());
        insertTo(&mut globals, ":", function_type(&var, &function_type(&list, &list)));
        for i in range(0 as uint, 10) {
            let (name, typ) = tuple_type(i);
            insertTo(&mut globals, name.as_slice(), typ);
        }
        TypeEnvironment {
            assemblies: Vec::new(),
            namedTypes : globals,
            local_types : HashMap::new(),
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
                    type_decl.context = FromVec::from_vec(vec_context);
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
                            .unwrap_or_else(|| if intern("[]") == op.name { KindFunction(box StarKind, box StarKind) } else { StarKind });
                    }
                    _ => ()
                }
                freshen_all(self, &mut subs, &mut instance.typ);
            }
            for binding in instance.bindings.mut_iter() {
                let decl = class.declarations.iter().find(|decl| binding.name.as_slice().ends_with(decl.name.as_slice()))
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
                    binding.typeDecl.context = FromVec::from_vec(vec_context);
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

            match module.bindings.mut_iter().find(|bind| bind.name.name == type_decl.name) {
                Some(bind) => {
                    bind.typeDecl = type_decl.clone();
                }
                None => fail!("Error: Type declaration for '{}' has no binding", type_decl.name)
            }
        }

        {
            let mut subs = Substitution { subs: HashMap::new(), constraints: HashMap::new() }; 
            self.typecheck_global_bindings(&mut subs, module);
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
        self.local_types.find(ident)
            .or_else(|| self.namedTypes.find(ident))
            .or_else(|| {
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
        FromVec::from_vec(result)
    }
    
    ///Searches through a type, comparing it with the type on the identifier, returning all the specialized constraints
    pub fn find_specialized_instances(&self, typ: &Type, actual_type: &Type) -> ~[(InternedStr, Type)] {
        let mut constraints = Vec::new();
        self.find_specialized(&mut constraints, actual_type, typ);
        if constraints.len() == 0 {
            fail!("Could not find the specialized instance between {} <-> {}", typ, actual_type);
        }
        FromVec::from_vec(constraints)
    }
    fn find_specialized(&self, constraints: &mut Vec<(InternedStr, Type)>, actual_type: &Type, typ: &Type) {
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

    fn apply_locals(&mut self, subs: &Substitution) {
        for (_, typ) in self.local_types.mut_iter() {
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
    fn has_instance(&self, class: InternedStr, searched_type: &Type) -> bool {
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
            &Literal(ref lit) => {
                match *lit {
                    Integral(_) => {
                        self.constraints.insert(expr.typ.var().clone(), vec![intern("Num")]);
                        match &mut expr.typ {
                            &TypeVariable(ref mut v) => v.kind = star_kind.clone(),
                            _ => ()
                        }
                    }
                    Fractional(_) => {
                        self.constraints.insert(expr.typ.var().clone(), vec![intern("Fractional")]);
                        match &mut expr.typ {
                            &TypeVariable(ref mut v) => v.kind = star_kind.clone(),
                            _ => ()
                        }
                    }
                    String(_) => {
                        expr.typ = list_type(char_type());
                    }
                    Char(_) => {
                        expr.typ = char_type();
                    }
                }   
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
                let mut argType = self.new_var();
                expr.typ = function_type(&argType, &self.new_var());

                {
                    self.typecheck_pattern(&expr.location, subs, arg, &mut argType);
                    self.typecheck(*body, subs);
                }
                replace(&mut self.constraints, &mut expr.typ, subs);
                with_arg_return(&mut expr.typ, |_, return_type| {
                    *return_type = body.typ.clone();
                });
            }
            &Let(ref mut bindings, ref mut body) => {

                {
                    self.typecheck_local_bindings(subs, &mut BindingsWrapper { value: *bindings });
                    self.apply_locals(subs);
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
                let mut previous = self.new_var_kind(KindFunction(box StarKind, box StarKind));
                self.constraints.insert(previous.var().clone(), vec!(intern("Monad")));
                previous = TypeApplication(box previous, box self.new_var());
                for bind in bindings.mut_iter() {
                    match *bind {
                        DoExpr(ref mut e) => {
                            self.typecheck(e, subs);
                            unify_location(self, subs, &e.location, &mut e.typ, &mut previous);
                        }
                        DoLet(ref mut bindings) => {
                            self.typecheck_local_bindings(subs, &mut BindingsWrapper { value: *bindings });
                            self.apply_locals(subs);
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
                self.local_types.insert(ident.clone(), typ.clone());
            }
            &NumberPattern(_) => {
                let mut typ = int_type();
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
                self.apply_locals(subs);
                self.pattern_rec(0, location, subs, *patterns, &mut t);
            }
            &WildCardPattern => {
                let mut typ = self.new_var();
                unify_location(self, subs, location, &mut typ, match_type);
                replace(&mut self.constraints, match_type, subs);
                replace(&mut self.constraints, &mut typ, subs);
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

    pub fn typecheck_mutually_recursive_bindings<'a>
            (&mut self
            , subs: &mut Substitution
            , bindings: &'a mut Bindings
            , is_global: bool) {
        let start_var_index = self.variableIndex + 1;
        
        let graph = build_graph(bindings);
        let groups = strongly_connected_components(&graph);

        for group in groups.iter() {
            for index in group.iter() {
                let bindIndex = graph.get_vertex(*index).value;
                let bind = bindings.get_mut(bindIndex);
                bind.expression.typ = self.new_var();
                if is_global {
                    self.namedTypes.insert(bind.name.clone(), bind.expression.typ.clone());
                }
                else {
                    self.local_types.insert(bind.name.clone(), bind.expression.typ.clone());
                }
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
                    debug!("End typecheck {} :: {}", bind.name, bind.expression.typ);
                }
                if is_global {
                    for bind in group.iter().map(|index| bindings.get_mut(graph.get_vertex(*index).value)) {
                        replace(&mut self.constraints, self.namedTypes.get_mut(&bind.name), subs);
                    }
                    self.local_types.clear();
                }
                else {
                    self.apply_locals(subs);
                }
            }
            if is_global {
                subs.subs.clear();
                subs.constraints.clear();
            }
            for index in group.iter() {
                let bindIndex = graph.get_vertex(*index).value;
                let bind = bindings.get_mut(bindIndex);
                bind.typeDecl.typ = bind.expression.typ.clone();
                bind.typeDecl.context = self.find_constraints(&bind.typeDecl.typ);
                let typ = if is_global {
                    self.namedTypes.get_mut(&bind.name)
                }
                else {
                    self.local_types.get_mut(&bind.name)
                };
                quantify(start_var_index, typ);
            }
        }
    }

    fn typecheck_local_bindings(&mut self, subs: &mut Substitution, bindings: &mut Bindings) {
        self.typecheck_mutually_recursive_bindings(subs, bindings, false);
    }
    fn typecheck_global_bindings(&mut self, subs: &mut Substitution, bindings: &mut Bindings) {
        self.typecheck_mutually_recursive_bindings(subs, bindings, true);
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
                        &TypeOperator(ref op) => op.name == intern("->"),
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
fn update_constraints(constraints: &mut HashMap<TypeVariable, Vec<InternedStr>>, old: &TypeVariable, new: &Type, subs: &Substitution) {
    match new {
        &TypeVariable(ref new_var) => {
            subs.constraints.find(old).map(|subs_constraints| {
                let to_update = constraints.find_or_insert(new_var.clone(), Vec::new());
                for c in subs_constraints.iter() {
                    if to_update.iter().find(|x| *x == c) == None {
                        to_update.push(c.clone());
                    }
                }
            });
        }
        _ => ()
    }
}

///Replace all typevariables using the substitution 'subs'
fn replace(constraints: &mut HashMap<TypeVariable, Vec<InternedStr>>, old : &mut Type, subs : &Substitution) {
    let replaced = match *old {
        TypeVariable(ref id) => {
            subs.subs.find(id).map(|new| {
                update_constraints(constraints, id, new, subs);
                new.clone()
            })
        }
        TypeApplication(ref mut lhs, ref mut rhs) => {
            replace(constraints, *lhs, subs);
            replace(constraints, *rhs, subs);
            None
        }
        _ => None, //fail!("replace called on Generic")
    };
    match replaced {
        Some(x) => *old = x,
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
    let result = match *typ {
        Generic(ref id) => freshen_var(env, subs, id),
        TypeApplication(ref mut lhs, ref mut rhs) => {
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
        &TypeVariable(ref id) => freshen_var(env, subs, id),
        &TypeApplication(ref mut lhs, ref mut rhs) => {
            freshen_all(env, subs, *lhs);
            freshen_all(env, subs, *rhs);
            None
        }
        _ => None
    };
    match result {
        Some(x) => *typ = x,
        None => ()
    }
}
fn freshen_var(env: &mut TypeEnvironment, subs: &mut Substitution, id: &TypeVariable) -> Option<Type> {
    subs.subs.find(id)
        .map(|var| var.clone())
        .or_else(|| {
        let new = env.new_var_kind(id.kind.clone());
        subs.subs.insert(id.clone(), new.clone());
        env.constraints.find(id)
            .map(|constraints| constraints.clone())
            .map(|c| env.constraints.insert(new.var().clone(), c));
        Some(new)
    })
}

///Takes two types and attempts to make them the same type
fn unify_location(env: &mut TypeEnvironment, subs: &mut Substitution, location: &Location, lhs: &mut Type, rhs: &mut Type) {
    debug!("Unifying {} <-> {}", *lhs, *rhs);
    match unify(env, subs, lhs.clone(), rhs.clone()) {
        Ok(typ) => {
            //Using unsafe here to avoid a very expensive copy of the substitution
            //Since 'subs.subs' is never resized but only has its elements modified
            //and calling find on 'subs2' will only return None for variables in 'typ'
            //since we have checked for recursive unifiction in unify
            let subs2 = unsafe { ::std::mem::transmute::<&Substitution, &mut Substitution>(subs) };
            for (_, ref mut typ) in subs.subs.mut_iter() {
                replace(&mut env.constraints, *typ, subs2);
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
    MissingInstance(InternedStr, Type, TypeVariable)
}

fn unify(env: &mut TypeEnvironment, subs: &mut Substitution, lhs: Type, rhs: Type) -> Result<Type, TypeError> {
    fn bind_variable(env: &mut TypeEnvironment, subs: &mut Substitution, var: TypeVariable, typ: Type) -> Result<Type, TypeError> {
        let x = match typ {
            TypeVariable(ref var2) => {
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
                                    match typ {
                                        TypeOperator(ref op) => {
                                            if *c == intern("Num") && (op.name == intern("Int") || op.name == intern("Double")) && *typ.kind() == star_kind {
                                                continue;
                                            }
                                            else if *c == intern("Fractional") && intern("Double") == op.name && *typ.kind() == star_kind {
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
                        Ok(typ) => Ok(TypeApplication(box arg, box typ)),
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

fn add_edges<T: 'static>(graph: &mut Graph<T>, map: &HashMap<Name, VertexIndex>, function_index: VertexIndex, expr: &TypedExpr<Name>) {
    struct EdgeVisitor<'a, T> {
        graph: &'a mut Graph<T>,
        map: &'a HashMap<Name, VertexIndex>,
        function_index: VertexIndex
    }
    impl <'a, T: 'static> Visitor<Name> for EdgeVisitor<'a, T> {
        fn visit_expr(&mut self, expr: &TypedExpr<Name>) {
            match expr.expr {
                Identifier(ref n) => {
                    match self.map.find(n) {
                        Some(index) => self.graph.connect(self.function_index, *index),
                        None => ()
                    }
                }
                _ => walk_expr(self, expr)
            }
        }
    }
    EdgeVisitor { graph: graph, map: map, function_index: function_index }.visit_expr(expr)
}

fn each_type(typ: &Type, mut var_fn: |&TypeVariable|, mut op_fn: |&TypeOperator|) {
    each_type_(typ, &mut var_fn, &mut op_fn);
}
fn each_type_(typ: &Type, var_fn: &mut |&TypeVariable|, op_fn: &mut |&TypeOperator|) {
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
fn find_kind(test: &TypeVariable, expected: Option<Kind>, typ: &Type) -> Result<Option<Kind>, &'static str> {
    match *typ {
        TypeVariable(ref var) if test.id == var.id => {
            match expected {
                Some(k) => {
                    if k != var.kind {
                        Err("Kinds do not match")
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
    Type::new_op(intern("->"), ~[func.clone(), arg.clone()])
}

pub fn function_type_(func : Type, arg : Type) -> Type {
    Type::new_op(intern("->"), ~[func, arg])
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
pub fn identifier(i : &str) -> TypedExpr {
    TypedExpr::new(Identifier(intern(i)))
}
#[cfg(test)]
pub fn lambda(arg : &str, body : TypedExpr) -> TypedExpr {
    TypedExpr::new(Lambda(IdentifierPattern(intern(arg)), box body))
}
#[cfg(test)]
pub fn number(i : int) -> TypedExpr {
    TypedExpr::new(Literal(Integral(i)))
}
#[cfg(test)]
pub fn rational(i : f64) -> TypedExpr {
    TypedExpr::new(Literal(Fractional(i)))
}
#[cfg(test)]
pub fn apply(func : TypedExpr, arg : TypedExpr) -> TypedExpr {
    TypedExpr::new(Apply(box func, box arg))
}
#[cfg(test)]
pub fn let_(bindings : ~[Binding], expr : TypedExpr) -> TypedExpr {
    TypedExpr::new(Let(bindings, box expr))
}
#[cfg(test)]
pub fn case(expr : TypedExpr, alts: ~[Alternative]) -> TypedExpr {
    TypedExpr::new(Case(box expr, alts))
}

pub fn do_typecheck(input: &str) -> Module<Name> {
    do_typecheck_with(input, [])
}
pub fn do_typecheck_with(input: &str, types: &[&DataTypes]) -> Module<Name> {
    let mut parser = ::parser::Parser::new(input.chars());
    let mut module = rename_module(parser.module());
    let mut env = TypeEnvironment::new();
    for t in types.iter() {
        env.add_types(*t);
    }
    env.typecheck_module(&mut module);
    module
}
pub fn typecheck_module(module: &str) -> IoResult<(Vec<Module<Name>>, TypeEnvironment)> {
    use parser::parse_modules;
    use renamer::rename_modules;
    let mut modules = rename_modules(try!(parse_modules(module)));
    let mut env = TypeEnvironment::new();
    for module in modules.mut_iter() {
        env.typecheck_module(module);
    }
    Ok((modules, env))
}


#[cfg(test)]
mod test {
use interner::*;
use module::*;
use typecheck::*;
use renamer::*;

use parser::Parser;
use std::io::File;

use test::Bencher;

#[test]
fn application() {
    let mut env = TypeEnvironment::new();
    let n = identifier("primIntAdd");
    let num = number(1);
    let e = apply(n, num);
    let mut expr = rename_expr(e);
    let unary_func = function_type_(int_type(), int_type());
    env.typecheck_expr(&mut expr);

    assert!(expr.typ == unary_func);
}

#[test]
fn typecheck_lambda() {
    let mut env = TypeEnvironment::new();
    let unary_func = function_type_(int_type(), int_type());

    let e = lambda("x", apply(apply(identifier("primIntAdd"), identifier("x")), number(1)));
    let mut expr = rename_expr(e);
    env.typecheck_expr(&mut expr);

    assert_eq!(expr.typ, unary_func);
}

#[test]
fn typecheck_let() {
    let mut env = TypeEnvironment::new();
    let unary_func = function_type_(int_type(), int_type());

    //let test x = add x in test
    let unary_bind = lambda("x", apply(apply(identifier("primIntAdd"), identifier("x")), number(1)));
    let e = let_(~[Binding { arity: 1, name: intern("test"), expression: unary_bind, typeDecl: Default::default() }], identifier("test"));
    let mut expr = rename_expr(e);
    env.typecheck_expr(&mut expr);

    assert_eq!(expr.typ, unary_func);
}

#[test]
fn typecheck_case() {
    let mut env = TypeEnvironment::new();
    let type_int = int_type();

    let mut parser = Parser::new(r"case [] of { : x xs -> primIntAdd x 2 ; [] -> 3}".chars());
    let mut expr = rename_expr(parser.expression_());
    env.typecheck_expr(&mut expr);

    assert_eq!(expr.typ, type_int);
    match &expr.expr {
        &Case(ref case_expr, _) => {
            assert_eq!(case_expr.typ, list_type(type_int));
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

    assert_eq!(module.bindings[1].expression.typ, int_type());
}

#[test]
fn typecheck_string() {
    let mut env = TypeEnvironment::new();

    let mut parser = Parser::new("\"hello\"".chars());
    let mut expr = rename_expr(parser.expression_());
    env.typecheck_expr(&mut expr);

    assert_eq!(expr.typ, list_type(char_type()));
}

#[test]
fn typecheck_tuple() {
    let mut env = TypeEnvironment::new();

    let mut parser = Parser::new("(primIntAdd 0 0, \"a\")".chars());
    let mut expr = rename_expr(parser.expression_());
    env.typecheck_expr(&mut expr);

    let list = list_type(char_type());
    assert_eq!(expr.typ, Type::new_op(intern("(,)"), ~[int_type(), list]));
}

#[test]
fn typecheck_module() {

    let file =
r"data Bool = True | False
test x = True";
    let module = do_typecheck(file);

    let typ = function_type_(Type::new_var(0), bool_type());
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

    
    let int_type = int_type();
    let list_type = list_type(int_type.clone());
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
    assert_eq!(typ, &int_type());
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
    let test = function_type_(Type::new_var(-1), function_type_(Type::new_var(-2), int_type()));
    assert_eq!(typ, &test);
    let test_cons = vec![intern("Test")];
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
    let list_type = list_type(Type::new_var(100));
    assert_eq!(*typ, function_type_(list_type.clone(), function_type_(list_type, bool_type())));
    let var = typ.appl().appr().appr().var();
    let eq = vec![intern("Eq")];
    assert_eq!(env.constraints.find(var), Some(&eq));
}

#[test]
fn typecheck_num_double() {

    let file = 
r"test x = primDoubleAdd 0 x";
    let module = do_typecheck(file);

    let typ = function_type_(double_type(), double_type());
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
    assert_eq!(main.expression.typ, Type::new_op(intern("Maybe"), ~[int_type()]));
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
    let module = do_typecheck(contents.as_slice());

    let id = module.bindings.iter().find(|bind| bind.name.as_slice() == "id");
    assert!(id != None);
    let id_bind = id.unwrap();
    assert_eq!(id_bind.expression.typ, function_type_(Type::new_var(0), Type::new_var(0)));
}

#[test]
fn typecheck_import() {
   
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let contents = File::open(path).read_to_str().unwrap();
        do_typecheck(contents.as_slice())
    };

    let file = 
r"
test1 = map not [True, False]
test2 = id (primIntAdd 2 0)";
    let module = do_typecheck_with(file, [&prelude as &DataTypes]);

    assert_eq!(module.bindings[0].name.as_slice(), "test1");
    assert_eq!(module.bindings[0].expression.typ, list_type(bool_type()));
    assert_eq!(module.bindings[1].name.as_slice(), "test2");
    assert_eq!(module.bindings[1].expression.typ, int_type());
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
        do_typecheck(contents.as_slice())
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
        do_typecheck(contents.as_slice())
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
    assert_eq!(module.bindings[0].typeDecl.context[0].class, intern("Monad"));
}

#[test]
fn binding_pattern() {
    let module = do_typecheck(r"
test f (: x xs) = f x : test f xs
test _ [] = []
");
    let a = Type::new_var(0);
    let b = Type::new_var(1);
    let test = function_type_(function_type_(a.clone(), b.clone()), function_type_(list_type(a), list_type(b)));
    assert_eq!(module.bindings[0].expression.typ, test);
}

#[test]
#[should_fail]
fn do_expr_wrong_monad() {
    
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let contents = File::open(path).read_to_str().unwrap();
        do_typecheck(contents.as_slice())
    };

    let file = 
r"
test x = do
    putStrLn x
    reverse [primIntAdd 0 0, 1, 2]";
    do_typecheck_with(file, [&prelude as &DataTypes]);
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
    let mut parser = Parser::new(contents.as_slice().chars());
    let module = rename_module(parser.module());

    b.iter(|| {
        let mut env = TypeEnvironment::new();
        let mut m = module.clone();
        env.typecheck_module(&mut m);
    });
}

}
