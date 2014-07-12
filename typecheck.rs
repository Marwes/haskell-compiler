use collections::HashMap;
use std::mem::swap;
use std::vec::FromVec;
use std::io::IoResult;
use module::*;
use graph::{Graph, VertexIndex, strongly_connected_components};
use builtins::builtins;
use renamer::*;
use interner::*;

pub use lexer::Location;
pub use module::Type;

#[cfg(test)]
use module::Alternative;

///Trait which can be implemented by types where types can be looked up by name
pub trait Types {
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Qualified<Type>>;
    fn find_class<'a>(&'a self, name: InternedStr) -> Option<(&'a [Constraint], &'a TypeVariable, &'a [TypeDeclaration])>;
    fn has_instance(&self, classname: InternedStr, typ: &Type) -> bool {
        match self.find_instance(classname, typ) {
            Some(_) => true,
            None => false
        }
    }
    fn find_instance<'a>(&'a self, classname: InternedStr, typ: &Type) -> Option<(&'a [Constraint], &'a Type)>;
    fn each_constraint_list(&self, |&[Constraint]|);
}

///A trait which also allows for lookup of data types
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
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Qualified<Type>> {
        for bind in self.bindings.iter() {
            if bind.name == *name {
                return Some(&bind.typ);
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

    fn find_class<'a>(&'a self, name: InternedStr) -> Option<(&'a [Constraint], &'a TypeVariable, &'a [TypeDeclaration])> {
        self.classes.iter()
            .find(|class| name == class.name)
            .map(|class| (class.constraints.as_slice(), &class.variable, class.declarations.as_slice()))
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
            func(bind.typ.constraints);
        }

        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                func(decl.typ.constraints);
            }
        }
    }
}

impl DataTypes for Module<Name> {
    fn find_data_type<'a>(&'a self, name: InternedStr) -> Option<&'a DataDefinition<Name>> {
        for data in self.dataDefinitions.iter() {
            if name == extract_applied_type(&data.typ.value).ctor().name {
                return Some(data);
            }
        }
        None
    }
}

///The TypeEnvironment stores most data which is needed as typechecking is performed.
pub struct TypeEnvironment<'a> {
    ///Stores references to imported modules or assemblies
    assemblies: Vec<&'a DataTypes>,
    ///A mapping of names to the type which those names are bound to.
    namedTypes : HashMap<Name, Qualified<Type>>,
    ///A mapping used for any variables declared inside any global binding.
    ///Used in conjuction to the global 'namedTypes' map since the local table can
    ///be cleared once those bindings are no longer in used which gives an overall speed up.
    local_types : HashMap<Name, Qualified<Type>>,
    ///Stores the constraints for each typevariable since the typevariables cannot themselves store this.
    constraints: HashMap<TypeVariable, Vec<InternedStr>>,
    ///Stores data about the instances which are available.
    ///1: Any constraints for the type which the instance is for
    ///2: The name of the class
    ///3: The Type which the instance is defined for
    instances: Vec<(~[Constraint], InternedStr, Type)>,
    classes: Vec<(~[Constraint], InternedStr)>,
    ///The current age for newly created variables.
    ///Age is used to determine whether variables need to be quantified or not.
    variable_age : int,
}

///A Substitution is a mapping from typevariables to types.
#[deriving(Clone)]
struct Substitution {
    ///A hashmap which contains what a typevariable is unified to.
    subs: HashMap<TypeVariable, Type>
}

///Trait which provides access to the bindings in a struct.
trait Bindings {
    fn get_mut<'a>(&'a mut self, idx: (uint, uint)) -> &'a mut [Binding<Name>];

    fn each_binding(&self, |&[Binding<Name>], (uint, uint)|);
}

impl Bindings for Module<Name> {
    fn get_mut<'a>(&'a mut self, (instance_idx, idx): (uint, uint)) -> &'a mut [Binding<Name>] {
        let bindings = if instance_idx == 0 {
            &mut self.bindings
        }
        else if instance_idx - 1 < self.instances.len() {
            &mut self.instances[instance_idx - 1].bindings
        }
        else {
            &mut self.classes[instance_idx - 1 - self.instances.len()].bindings
        };
        mut_bindings_at(*bindings, idx)
    }

    fn each_binding(&self, func: |&[Binding<Name>], (uint, uint)|) {
        let mut index = 0;
        for binds in binding_groups(self.bindings.as_slice()) {
            func(binds, (0, index));
            index += binds.len();
        }
        for (instance_index, instance) in self.instances.iter().enumerate() {
            index = 0;
            for binds in binding_groups(instance.bindings.as_slice()) {
                func(binds, (instance_index + 1, index));
                index += binds.len();
            }
        }
        for (class_index, class) in self.classes.iter().enumerate() {
            index = 0;
            for binds in binding_groups(class.bindings.as_slice()) {
                func(binds, (class_index + 1 + self.instances.len(), index));
                index += binds.len();
            }
        }
    }
}

fn mut_bindings_at<'a, Ident: Eq>(bindings: &'a mut [Binding<Ident>], idx: uint) -> &'a mut [Binding<Ident>] {
    let end = bindings
        .slice_from(idx)
        .iter()
        .position(|bind| bind.name != bindings[idx].name)
        .unwrap_or(bindings.len() - idx);
    bindings.mut_slice(idx, idx + end)
}

//Woraround since traits around a vector seems problematic
struct BindingsWrapper<'a> {
    value: &'a mut [Binding<Name>]
}

impl <'a> Bindings for BindingsWrapper<'a> {
    fn get_mut<'a>(&'a mut self, (_, idx): (uint, uint)) -> &'a mut [Binding<Name>] {
        mut_bindings_at(self.value, idx)
    }

    fn each_binding(&self, func: |&[Binding<Name>], (uint, uint)|) {
        let mut index = 0;
        for binds in binding_groups(self.value.as_slice()) {
            func(binds, (0, index));
            index += binds.len();
        }
    }
}

fn insert_to(map: &mut HashMap<Name, Qualified<Type>>, name: &str, typ: Type) {
    map.insert(Name { name: intern(name), uid: 0 }, qualified(~[], typ));
}
fn prim(typename: &str, op: &str) -> String {
    let mut b = String::from_str("prim");
    b.push_str(typename);
    b.push_str(op);
    b
}
fn add_primitives(globals: &mut HashMap<Name, Qualified<Type>>, typename: &str) {
    let typ = Type::new_op(intern(typename), ~[]);
    {
        let binop = function_type(&typ, &function_type(&typ, &typ));
        insert_to(globals, prim(typename, "Add").as_slice(), binop.clone());
        insert_to(globals, prim(typename, "Subtract").as_slice(), binop.clone());
        insert_to(globals, prim(typename, "Multiply").as_slice(), binop.clone());
        insert_to(globals, prim(typename, "Divide").as_slice(), binop.clone());
        insert_to(globals, prim(typename, "Remainder").as_slice(), binop.clone());
    }
    {
        let binop = function_type_(typ.clone(), function_type_(typ, bool_type()));
        insert_to(globals, prim(typename, "EQ").as_slice(), binop.clone());
        insert_to(globals, prim(typename, "LT").as_slice(), binop.clone());
        insert_to(globals, prim(typename, "LE").as_slice(), binop.clone());
        insert_to(globals, prim(typename, "GT").as_slice(), binop.clone());
        insert_to(globals, prim(typename, "GE").as_slice(), binop.clone());
    }
}

impl <'a> TypeEnvironment<'a> {

    ///Creates a new TypeEnvironment and adds all the primitive types
    pub fn new() -> TypeEnvironment {
        let mut globals = HashMap::new();
        add_primitives(&mut globals, "Int");
        add_primitives(&mut globals, "Double");
        insert_to(&mut globals,"primIntToDouble", function_type_(int_type(), double_type()));
        insert_to(&mut globals, "primDoubleToInt", function_type_(double_type(), int_type()));
        let var = Generic(Type::new_var_kind(intern("a"), star_kind.clone()).var().clone());
        
        for (name, typ) in builtins().move_iter() {
            insert_to(&mut globals, name, typ);
        }
        let list = list_type(var.clone());
        insert_to(&mut globals, "[]", list.clone());
        insert_to(&mut globals, ":", function_type(&var, &function_type(&list, &list)));
        insert_to(&mut globals, "()", unit());
        for i in range(2 as uint, 10) {
            let (name, typ) = tuple_type(i);
            insert_to(&mut globals, name.as_slice(), typ);
        }
        TypeEnvironment {
            assemblies: Vec::new(),
            namedTypes : globals,
            local_types : HashMap::new(),
            constraints: HashMap::new(),
            instances: Vec::new(),
            classes: Vec::new(),
            variable_age : 0 ,
        }
    }

    pub fn add_types(&'a mut self, types: &'a DataTypes) {
        self.assemblies.push(types);
    }

    ///Typechecks a module
    ///If the typecheck is successful the types in the module are updated with the new types.
    ///If any errors were found while typechecking fail! is called.
    pub fn typecheck_module(&mut self, module: &mut Module<Name>) {
        let start_var_age = self.variable_age + 1;
        for data_def in module.dataDefinitions.mut_iter() {
            for constructor in data_def.constructors.mut_iter() {
                let mut typ = constructor.typ.clone();
                quantify(0, &mut typ);
                self.namedTypes.insert(constructor.name.clone(), typ);
            }
        }
        for class in module.classes.mut_iter() {
            //Instantiate a new variable and replace all occurances of the class variable with this
            let mut var_kind = None;
            for type_decl in class.declarations.mut_iter() {
                var_kind = match find_kind(&class.variable, var_kind, &type_decl.typ.value) {
                    Ok(k) => k,
                    Err(msg) => fail!("{}", msg)
                };
                //If we found the variable, update it immediatly since the kind of th variable
                //matters when looking for constraints, etc
                match var_kind {
                    Some(ref k) => {
                        class.variable.kind.clone_from(k);
                    }
                    None => ()
                }
                
                let c = Constraint { class: class.name.clone(), variables: ~[class.variable.clone()] };
                {//Workaround to add the class's constraints directyly to the declaration
                    let mut context = ~[];
                    swap(&mut context, &mut type_decl.typ.constraints);
                    let mut vec_context: Vec<Constraint> = context.move_iter().collect();
                    vec_context.push(c);
                    type_decl.typ.constraints = FromVec::from_vec(vec_context);
                }
                let mut t = type_decl.typ.clone();
                quantify(0, &mut t);
                self.namedTypes.insert(Name { name: type_decl.name.clone(), uid: 0 }, t);
            }
            self.classes.push((class.constraints.clone(), class.name.clone()));
        }
        let data_definitions = module.dataDefinitions.clone();
        for instance in module.instances.mut_iter() {
            let class = module.classes.iter().find(|class| class.name == instance.classname)
                .expect(format!("Could not find class {}", instance.classname));
            //Update the kind of the type for the instance to be the same as the class kind (since we have no proper kind inference
            match instance.typ {
                TypeConstructor(ref mut op) => {
                    let maybe_data = self.assemblies.iter().filter_map(|a| a.find_data_type(op.name))
                        .next();
                    op.kind = maybe_data
                        .or_else(|| data_definitions.iter().find(|data| op.name == extract_applied_type(&data.typ.value).ctor().name))
                        .map(|data| extract_applied_type(&data.typ.value).kind().clone())
                        .unwrap_or_else(|| if intern("[]") == op.name { KindFunction(box StarKind, box StarKind) } else { StarKind });
                }
                _ => ()
            }
            for binding in instance.bindings.mut_iter() {
                let decl = class.declarations.iter().find(|decl| binding.name.as_slice().ends_with(decl.name.as_slice()))
                    .expect(format!("Could not find {} in class {}", binding.name, class.name));
                binding.typ = decl.typ.clone();
                replace_var(&mut binding.typ.value, &class.variable, &instance.typ);
                self.freshen_qualified_type(&mut binding.typ, HashMap::new());
                {
                    let mut context = ~[];
                    swap(&mut context, &mut binding.typ.constraints);
                    let mut vec_context: Vec<Constraint> = context.move_iter().collect();
                    for constraint in instance.constraints.iter() {
                        vec_context.push(constraint.clone());
                    }
                    binding.typ.constraints = FromVec::from_vec(vec_context);
                }
            }
            {
                let mut missing_super_classes = self.find_class_constraints(class.name)
                    .unwrap_or_else(|| fail!("Error: Missing class {}", class.name))
                    .iter()//Make sure we have an instance for all of the constraints
                    .filter(|constraint| !self.has_instance(constraint.class, &instance.typ))
                    .peekable();
                if !missing_super_classes.is_empty() {
                    let mut buffer = String::new();
                    buffer.push_str(missing_super_classes.next().unwrap().class.as_slice());
                    for constraint in missing_super_classes {
                        buffer.push_str(", ");
                        buffer.push_str(constraint.class.as_slice());
                    }
                    fail!("The type {} does not have all necessary super class instances required for {}.\n Missing: {}",
                        instance.typ, instance.classname, buffer);
                }
            }
            self.instances.push((instance.constraints.clone(), instance.classname.clone(), instance.typ.clone()));
        }
        
        for type_decl in module.typeDeclarations.mut_iter() {

            match module.bindings.mut_iter().find(|bind| bind.name.name == type_decl.name) {
                Some(bind) => {
                    bind.typ = type_decl.typ.clone();
                }
                None => fail!("Error: Type declaration for '{}' has no binding", type_decl.name)
            }
        }

        {
            let mut subs = Substitution { subs: HashMap::new() }; 
            self.typecheck_global_bindings(start_var_age, &mut subs, module);
        }
    }

    ///Typechecks an expression.
    ///The types in the expression are updated with the correct types.
    ///If the expression has a type error, fail is called.
    pub fn typecheck_expr(&mut self, expr : &mut TypedExpr<Name>) {
        let mut subs = Substitution { subs: HashMap::new() }; 
        let mut typ = self.typecheck(expr, &mut subs);
        unify_location(self, &mut subs, &expr.location, &mut typ, &mut expr.typ);
        self.substitute(&mut subs, expr);
    }

    ///Returns the type which is bound to the Name or None if the Name does not exist.
    pub fn find(&'a self, ident: &Name) -> Option<&'a Qualified<Type>> {
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
                        if result.iter().find(|x| x.class == *c && x.variables[0] == *var) == None {
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
    
    fn freshen_qualified_type(&mut self, typ: &mut Qualified<Type>, mut mapping: HashMap<TypeVariable, Type>) {
        for constraint in typ.constraints.mut_iter() {
            let old = constraint.variables[0].clone();
            let new = mapping.find_or_insert(old.clone(), self.new_var_kind(old.kind.clone()));
            constraint.variables[0] = new.var().clone();
        }
        let mut subs = Substitution { subs: mapping };
        freshen_all(self, &mut subs, &mut typ.value);
    }
    fn apply_locals(&mut self, subs: &Substitution) {
        for (_, typ) in self.local_types.mut_iter() {
            replace(&mut self.constraints, &mut typ.value, subs);
        }
    }

    ///Walks through an expression and applies the substitution on each of its types
    fn substitute(&mut self, subs : &Substitution, expr: &mut TypedExpr<Name>) {
        replace(&mut self.constraints, &mut expr.typ, subs);
        match expr.expr {
            Apply(ref mut func, ref mut arg) => {
                self.substitute(subs, *func);
                self.substitute(subs, *arg);
            }
            OpApply(ref mut lhs, _, ref mut rhs) => {
                self.substitute(subs, *lhs);
                self.substitute(subs, *rhs);
            }
            Let(ref mut bindings, ref mut let_expr) => {
                for bind in bindings.mut_iter() {
                    match bind.matches {
                        Simple(ref mut e) => self.substitute(subs, e),
                        Guards(ref mut gs) => {
                            for guard in gs.mut_iter() {
                                self.substitute(subs, &mut guard.predicate);
                                self.substitute(subs, &mut guard.expression);
                            }
                        }
                    }
                }
                self.substitute(subs, *let_expr);
            }
            Case(ref mut case_expr, ref mut alts) => {
                self.substitute(subs, *case_expr);
                for alt in alts.mut_iter() {
                    match alt.matches {
                        Simple(ref mut e) => self.substitute(subs, e),
                        Guards(ref mut gs) => {
                            for guard in gs.mut_iter() {
                                self.substitute(subs, &mut guard.predicate);
                                self.substitute(subs, &mut guard.expression);
                            }
                        }
                    }
                }
            }
            Lambda(_, ref mut body) => self.substitute(subs, *body),
            Do(ref mut binds, ref mut expr) => {
                for bind in binds.mut_iter() {
                    match *bind {
                        DoExpr(ref mut expr) => self.substitute(subs, expr),
                        DoBind(_, ref mut expr) => self.substitute(subs, expr),
                        DoLet(ref mut bindings) => {
                            for bind in bindings.mut_iter() {
                                match bind.matches {
                                    Simple(ref mut e) => self.substitute(subs, e),
                                    Guards(ref mut gs) => {
                                        for guard in gs.mut_iter() {
                                            self.substitute(subs, &mut guard.predicate);
                                            self.substitute(subs, &mut guard.expression);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                self.substitute(subs, *expr);
            }
            TypeSig(ref mut expr, _) => self.substitute(subs, *expr),
            Paren(ref mut expr) => self.substitute(subs, *expr),
            Identifier(..) | Literal(..) => ()
        }
    }

    ///Returns whether the type 'searched_type' has an instance for 'class'
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

    fn find_class_constraints(&'a self, class: InternedStr) -> Option<&'a [Constraint]> {
        self.classes.iter()
            .find(|& &(_, ref name)| *name == class)
            .map(|x| x.ref0().as_slice())
            .or_else(|| self.assemblies.iter()
                .filter_map(|types| types.find_class(class))//Find the class
                .next()//next will get us the first class (but should only be one)
                .map(|(constraints, _, _)| constraints))
    }

    ///Checks whether 'actual_type' fulfills all the constraints that the instance has.
    fn check_instance_constraints(&self, constraints: &[Constraint], instance_type: &Type, actual_type: &Type) -> bool {
        match (instance_type, actual_type) {
            (&TypeApplication(ref lvar, box TypeVariable(ref rvar)), &TypeApplication(ref ltype, ref rtype)) => {
                let maybeConstraint = constraints.iter().find(|c| c.variables[0] == *rvar);
                match maybeConstraint {
                    Some(constraint) => self.has_instance(constraint.class, *rtype)
                                     && self.check_instance_constraints(constraints, *lvar, *ltype),
                    None => false//?
                }
            }
            (&TypeConstructor(ref l), &TypeConstructor(ref r)) => l.name == r.name,
            (_, &TypeVariable(_)) => true,
            _ => false
        }
    }
    ///Creates a new type variable with a kind
    fn new_var_kind(&mut self, kind: Kind) -> Type {
        self.variable_age += 1;
        let mut var = Type::new_var_kind(intern(self.variable_age.to_str().as_slice()), kind);
        match var {
            TypeVariable(ref mut var) => var.age = self.variable_age,
            _ => ()
        }
        var
    }

    ///Creates a new type variable with the kind StarKind
    fn new_var(&mut self) -> Type {
        self.new_var_kind(StarKind)
    }

    ///Typechecks a Match
    fn typecheck_match(&mut self, matches: &mut Match<Name>, subs: &mut Substitution) -> Type {
        match *matches {
            Simple(ref mut e) => {
                let mut typ = self.typecheck(e, subs);
                unify_location(self, subs, &e.location, &mut typ, &mut e.typ);
                typ
            }
            Guards(ref mut gs) => {
                let mut typ = None;
                for guard in gs.mut_iter() {
                    let mut typ2 = self.typecheck(&mut guard.expression, subs);
                    unify_location(self, subs, &guard.expression.location, &mut typ2, &mut guard.expression.typ);
                    match typ {
                        Some(mut typ) => unify_location(self, subs, &guard.expression.location, &mut typ, &mut typ2),
                        None => ()
                    }
                    typ = Some(typ2);
                    let mut predicate = self.typecheck(&mut guard.predicate, subs);
                    unify_location(self, subs, &guard.predicate.location, &mut predicate, &mut bool_type());
                    unify_location(self, subs, &guard.predicate.location, &mut predicate, &mut guard.predicate.typ);
                }
                typ.unwrap()
            }
        }
    }

    ///Typechecks an expression
    fn typecheck(&mut self, expr : &mut TypedExpr<Name>, subs: &mut Substitution) -> Type {
        if expr.typ == Type::new_var(intern("a")) {
            expr.typ = self.new_var();
        }

        let x = match expr.expr {
            Literal(ref lit) => {
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
                expr.typ.clone()
            }
            Identifier(ref name) => {
                match self.fresh(name) {
                    Some(t) => {
                        debug!("{} as {}", name, t);
                        expr.typ = t.clone();
                        t
                    }
                    None => fail!("Undefined identifier '{}' at {}", *name, expr.location)
                }
            }
            Apply(ref mut func, ref mut arg) => {
                let func_type = self.typecheck(*func, subs);
                self.typecheck_apply(&expr.location, subs, func_type, *arg)
            }
            OpApply(ref mut lhs, ref op, ref mut rhs) => {
                let op_type = match self.fresh(op) {
                    Some(typ) => typ,
                    None => fail!("Undefined identifier '{}' at {}", *op, expr.location)
                };
                let first = self.typecheck_apply(&expr.location, subs, op_type, *lhs);
                self.typecheck_apply(&expr.location, subs, first, *rhs)
            }
            Lambda(ref arg, ref mut body) => {
                let mut argType = self.new_var();
                let mut result = function_type_(argType.clone(), self.new_var());

                self.typecheck_pattern(&expr.location, subs, arg, &mut argType);
                let body_type = self.typecheck(*body, subs);
                with_arg_return(&mut result, |_, return_type| {
                    *return_type = body_type.clone();
                });
                result
            }
            Let(ref mut bindings, ref mut body) => {
                self.typecheck_local_bindings(subs, &mut BindingsWrapper { value: *bindings });
                self.apply_locals(subs);
                self.typecheck(*body, subs)
            }
            Case(ref mut case_expr, ref mut alts) => {
                let mut match_type = self.typecheck(*case_expr, subs);
                self.typecheck_pattern(&alts[0].pattern.location, subs, &alts[0].pattern.node, &mut match_type);
                let mut alt0_ = self.typecheck_match(&mut alts[0].matches, subs);
                for alt in alts.mut_iter().skip(1) {
                    self.typecheck_pattern(&alt.pattern.location, subs, &alt.pattern.node, &mut match_type);
                    let mut alt_type = self.typecheck_match(&mut alt.matches, subs);
                    unify_location(self, subs, &alt.pattern.location, &mut alt0_, &mut alt_type);
                }
                alt0_
            }
            Do(ref mut bindings, ref mut last_expr) => {
                let mut previous = self.new_var_kind(KindFunction(box StarKind, box StarKind));
                self.constraints.insert(previous.var().clone(), vec!(intern("Monad")));
                previous = TypeApplication(box previous, box self.new_var());
                for bind in bindings.mut_iter() {
                    match *bind {
                        DoExpr(ref mut e) => {
                            let mut typ = self.typecheck(e, subs);
                            unify_location(self, subs, &e.location, &mut typ, &mut previous);
                        }
                        DoLet(ref mut bindings) => {
                            self.typecheck_local_bindings(subs, &mut BindingsWrapper { value: *bindings });
                            self.apply_locals(subs);
                        }
                        DoBind(ref mut pattern, ref mut e) => {
                            let mut typ = self.typecheck(e, subs);
                            unify_location(self, subs, &e.location, &mut typ, &mut previous);
                            let inner_type = match typ {
                                TypeApplication(_, ref mut t) => t,
                                _ => fail!("Not a monadic type: {}", typ)
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
                let mut typ = self.typecheck(*last_expr, subs);
                unify_location(self, subs, &last_expr.location, &mut typ, &mut previous);
                typ
            }
            TypeSig(ref mut expr, ref mut qualified_type) => {
                let mut typ = self.typecheck(*expr, subs);
                self.freshen_qualified_type(qualified_type, HashMap::new());
                match_or_fail(self, subs, &expr.location, &mut typ, &mut qualified_type.value);
                typ
            }
            Paren(ref mut expr) => self.typecheck(*expr, subs)
        };
        debug!("{}\nas\n{}", expr, x);
        x
    }
    fn typecheck_apply(&mut self, location: &Location, subs: &mut Substitution, mut func_type: Type, arg: &mut TypedExpr<Name>) -> Type {
        let arg_type = self.typecheck(arg, subs);
        let mut result = function_type_(arg_type, self.new_var());
        unify_location(self, subs, location, &mut func_type, &mut result);
        result = match result {
            TypeApplication(_, x) => *x,
            _ => fail!("Must be a type application (should be a function type), found {}", result)
        };
        result
    }
    ///Typechecks a pattern.
    ///Checks that the pattern has the type 'match_type' and adds all variables in the pattern.
    fn typecheck_pattern(&mut self, location: &Location, subs: &mut Substitution, pattern: &Pattern<Name>, match_type: &mut Type) {
        match pattern {
            &IdentifierPattern(ref ident) => {
                self.local_types.insert(ident.clone(), qualified(~[], match_type.clone()));
            }
            &NumberPattern(_) => {
                let mut typ = int_type();
                unify_location(self, subs, location, &mut typ, match_type);
            }
            &ConstructorPattern(ref ctorname, ref patterns) => {
                let mut t = self.fresh(ctorname)
	.expect(format!("Undefined constructer '{}' when matching pattern", *ctorname));
                let mut data_type = get_returntype(&t);
                
                unify_location(self, subs, location, &mut data_type, match_type);
                replace(&mut self.constraints, &mut t, subs);
                self.apply_locals(subs);
                self.pattern_rec(0, location, subs, *patterns, &mut t);
            }
            &WildCardPattern => {
            }
        }
    }
    ///Walks through the arguments of a pattern and typechecks each of them.
    fn pattern_rec(&mut self, i: uint, location: &Location, subs: &mut Substitution, patterns: &[Pattern<Name>], func_type: &mut Type) {
        if i < patterns.len() {
            let p = &patterns[i];
            with_arg_return(func_type, |arg_type, return_type| {
                self.typecheck_pattern(location, subs, p, arg_type);
                self.pattern_rec(i + 1, location, subs, patterns, return_type);
            });
        }
    }

    ///Typechecks a group of bindings such as
    ///map f (x:xs) = ...
    ///map f [] = ...
    fn typecheck_binding_group(&mut self, subs: &mut Substitution, bindings: &mut [Binding<Name>]) {
        debug!("Begin typecheck {} :: {}", bindings[0].name, bindings[0].typ);
        let mut argument_types = Vec::from_fn(bindings[0].arguments.len(), |_| self.new_var());
        let type_var = match bindings[0].typ.value {
            TypeVariable(ref var) => Some(var.clone()),
            _ => None
        };
        let mut previous_type = None;
        for bind in bindings.mut_iter() {
            if argument_types.len() != bind.arguments.len() {
                fail!("Binding {} do not have the same number of arguments", bind.name);//TODO re add location
            }
            for (arg, typ) in bind.arguments.mut_iter().zip(argument_types.mut_iter()) {
                self.typecheck_pattern(&Location::eof(), subs, arg, typ);
            }
            fn make_function(arguments: &[Type], expr: &Type) -> Type {
                if arguments.len() == 0 { expr.clone() }
                else { function_type_(arguments[0].clone(), make_function(arguments.slice_from(1), expr)) }
            }
            let mut typ = self.typecheck_match(&mut bind.matches, subs);
            typ = make_function(argument_types.as_slice(), &typ);
            match previous_type {
                Some(mut prev) => unify_location(self, subs, bind.matches.location(), &mut typ, &mut prev),
                None => ()
            }
            replace(&mut self.constraints, &mut typ, subs);
            previous_type = Some(typ);
        }
        let mut final_type = previous_type.unwrap();
        //HACK, assume that if the type declaration is only a variable it has no type declaration
        //In that case we need to unify that variable to 'typ' to make sure that environment becomes updated
        //Otherwise a type declaration exists and we need to do a match to make sure that the type is not to specialized
        if type_var.is_none() {
            match_or_fail(self, subs, &Location::eof(), &mut final_type, &bindings[0].typ.value);
        }
        else {
            unify_location(self, subs, &Location::eof(), &mut final_type, &mut bindings[0].typ.value);
        }
        match type_var {
            Some(var) => { subs.subs.insert(var, final_type); }
            None => ()
        }
        for bind in bindings.mut_iter() {
            match bind.matches {
                Simple(ref mut e) => self.substitute(subs, e),
                Guards(ref mut gs) => {
                    for g in gs.mut_iter() {
                        self.substitute(subs, &mut g.predicate);
                        self.substitute(subs, &mut g.expression);
                    }
                }
            }
        }
        debug!("End typecheck {} :: {}", bindings[0].name, bindings[0].typ);
    }
    
    ///Typechecks a set of bindings which may be mutually recursive
    ///Takes the minimum age that a variable created for this group can have, the current substitution, a set of bindings,
    ///and a global indicating wheter the bindings are global (true if at the module level, false otherwise, ex. 'let' binding)
    pub fn typecheck_mutually_recursive_bindings<'a>
            (&mut self
            , start_var_age: int
            , subs: &mut Substitution
            , bindings: &'a mut Bindings
            , is_global: bool) {
        
        let graph = build_graph(bindings);
        let groups = strongly_connected_components(&graph);

        for group in groups.iter() {
            for index in group.iter() {
                let bindIndex = graph.get_vertex(*index).value;
                let binds = bindings.get_mut(bindIndex);
                for bind in binds.mut_iter() {
                    if bind.typ.value == Type::new_var(intern("a")) {
                        bind.typ.value = self.new_var();
                    }
                }
                if is_global {
                    self.namedTypes.insert(binds[0].name.clone(), binds[0].typ.clone());
                }
                else {
                    self.local_types.insert(binds[0].name.clone(), binds[0].typ.clone());
                }
            }
            for index in group.iter() {
                {
                    let bindIndex = graph.get_vertex(*index).value;
                    let binds = bindings.get_mut(bindIndex);
                    self.typecheck_binding_group(subs, binds);
                }
                if is_global {
                    for bind in group.iter().flat_map(|index| bindings.get_mut(graph.get_vertex(*index).value).iter()) {
                        replace(&mut self.constraints, &mut self.namedTypes.get_mut(&bind.name).value, subs);
                    }
                    self.local_types.clear();
                }
                else {
                    self.apply_locals(subs);
                }
            }
            for index in group.iter() {
                let bindIndex = graph.get_vertex(*index).value;
                let binds = bindings.get_mut(bindIndex);
                for constraint in binds[0].typ.constraints.iter() {
                    self.insert_constraint(&constraint.variables[0], constraint.class.clone());
                }
                for bind in binds.mut_iter() {
                    {
                        let typ = if is_global {
                            self.namedTypes.get_mut(&bind.name)
                        }
                        else {
                            self.local_types.get_mut(&bind.name)
                        };
                        bind.typ = typ.clone();
                        quantify(start_var_age, typ);
                    }
                    bind.typ.constraints = self.find_constraints(&bind.typ.value);
                }
                debug!("End typecheck {} :: {}", binds[0].name, binds[0].typ);
            }
            if is_global {
                subs.subs.clear();
                self.constraints.clear();
            }
        }
    }
    ///Typechecks a group of local bindings (such as a let expression)
    fn typecheck_local_bindings(&mut self, subs: &mut Substitution, bindings: &mut Bindings) {
        self.typecheck_mutually_recursive_bindings(self.variable_age + 1, subs, bindings, false);
    }
    ///Typechecks a group of global bindings.
    fn typecheck_global_bindings(&mut self, start_var_age: int, subs: &mut Substitution, bindings: &mut Bindings) {
        self.typecheck_mutually_recursive_bindings(start_var_age, subs, bindings, true);
    }
    
    ///Workaround to make all imported functions quantified without requiring their type variables to be generic
    fn find_fresh(&self, name: &Name) -> Option<Qualified<Type>> {
        self.local_types.find(name)
            .or_else(|| self.namedTypes.find(name))
            .map(|x| x.clone())
            .or_else(|| {
            for types in self.assemblies.iter() {
                let v = types.find_type(name).map(|x| x.clone());
                match v {
                    Some(mut typ) => {
                        quantify(0, &mut typ);
                        return Some(typ);
                    }
                    None => ()
                }
            }
            None
        })
    }
    ///Instantiates new typevariables for every typevariable in the type found at 'name'
    fn fresh(&'a mut self, name: &Name) -> Option<Type> {
        match self.find_fresh(name) {
            Some(mut typ) => {
                let mut subs = Substitution { subs: HashMap::new() };
                freshen(self, &mut subs, &mut typ);
                for c in typ.constraints.iter() {
                    self.insert_constraint(&c.variables[0], c.class.clone());
                }
                Some(typ.value)
            }
            None => None
        }
    }
    
    
    fn insert_constraint(&mut self, var: &TypeVariable, classname: InternedStr) {
        let mut constraints = self.constraints.pop(var).unwrap_or(Vec::new());
        self.insert_constraint_(&mut constraints, var, classname);
        self.constraints.insert(var.clone(), constraints);
    }
    fn insert_constraint_(&mut self, constraints: &mut Vec<InternedStr>, var: &TypeVariable, classname: InternedStr) {
        let mut ii = 0;
        while ii < constraints.len() {
            if *constraints.get(ii) == classname || self.exists_as_super_class(*constraints.get(ii), classname) {
                //'classname' was already in the list, or existed as a sub class to the element
                return;
            }
            if self.exists_as_super_class(classname, *constraints.get(ii)) {
                //There is already a constraint which is a super class of classname,
                //replace that class with this new one
                *constraints.get_mut(ii) = classname;
                return;
            }
            ii += 1;
        }
        constraints.push(classname);
    }

    ///Checks if 'classname' exists as a super class to any
    fn exists_as_super_class(&self, constraint: InternedStr, classname: InternedStr) -> bool {
        match self.find_class_constraints(constraint) {
            Some(constraints) => {
                constraints.iter()
                    .any(|super_class| super_class.class == classname
                                    || self.exists_as_super_class(super_class.class, classname))
            }
            None => false
        }
    }
}


///Searches through a type, comparing it with the type on the identifier, returning all the specialized constraints
pub fn find_specialized_instances(typ: &Type, actual_type: &Type, constraints: &[Constraint]) -> ~[(InternedStr, Type)] {
    let mut result = Vec::new();
    find_specialized(&mut result, actual_type, typ, constraints);
    if constraints.len() == 0 {
        fail!("Could not find the specialized instance between {} <-> {}", typ, actual_type);
    }
    FromVec::from_vec(result)
}
fn find_specialized(result: &mut Vec<(InternedStr, Type)>, actual_type: &Type, typ: &Type, constraints: &[Constraint]) {
    match (actual_type, typ) {
        (_, &TypeVariable(ref var)) => {
            for c in constraints.iter().filter(|c| c.variables[0] == *var) {
                if result.iter().find(|x| *x.ref0() == c.class) == None {
                    result.push((c.class.clone(), actual_type.clone()));
                }
            }
        }
        (&TypeApplication(ref lhs1, ref rhs1), &TypeApplication(ref lhs2, ref rhs2)) => {
            find_specialized(result, *lhs1, *lhs2, constraints);
            find_specialized(result, *rhs1, *rhs2, constraints);
        }
        (_, &Generic(ref var)) => {
            for c in constraints.iter().filter(|c| c.variables[0] == *var) {
                if result.iter().find(|x| *x.ref0() == c.class) == None {
                    result.push((c.class.clone(), actual_type.clone()));
                }
            }
        }
        _ => ()
    }
}

///Quantifies all type variables with an age greater that start_var_age
///A quantified variable will when it is instantiated have new type variables
fn quantify(start_var_age: int, typ: &mut Qualified<Type>) {
    fn quantify_(start_var_age: int, typ: &mut Type) {
        let x = match typ {
            &TypeVariable(ref id) if id.age >= start_var_age => Some(id.clone()),
            &TypeApplication(ref mut lhs, ref mut rhs) => {
                quantify_(start_var_age, *lhs);
                quantify_(start_var_age, *rhs);
                None
            }
            _ => None
        };
        match x {
            Some(var) => *typ = Generic(var),
            None => ()
        }
    }
    for constraint in typ.constraints.mut_iter() {
        if constraint.variables[0].age > start_var_age {
            //constraint.variables[0] = Generic(constraint.variables[0].clone())
        }
    }
    quantify_(start_var_age, &mut typ.value);
}

///Replaces all occurences of 'var' in 'typ' with the the type 'replacement'
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
        &TypeConstructor(_) => None,
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
///Returns true if the type is a function
fn is_function(typ: &Type) -> bool {
    match typ {
        &TypeApplication(ref lhs, _) => {
            let l: &Type = *lhs;
            match l  {
                &TypeApplication(ref lhs, _) => {
                    let l: &Type = *lhs;
                    match l {
                        &TypeConstructor(ref op) => op.name == intern("->"),
                        _ => false
                    }
                }
                _ => false
            }
        }
        _ => false
    }
}
///Extracts the final return type of a type
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

///Replace all typevariables using the substitution 'subs'
fn replace(constraints: &mut HashMap<TypeVariable, Vec<InternedStr>>, old : &mut Type, subs : &Substitution) {
    let replaced = match *old {
        TypeVariable(ref id) => {
            subs.subs.find(id).map(|new| {
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

///Freshen creates new type variables at every position where Generic(..) appears.
fn freshen(env: &mut TypeEnvironment, subs: &mut Substitution, typ: &mut Qualified<Type>) {
    debug!("Freshen {}", typ);
    fn freshen_(env: &mut TypeEnvironment, subs: &mut Substitution, constraints: &[Constraint], typ: &mut Type) {
        let result = match *typ {
            Generic(ref id) => freshen_var(env, subs, constraints, id),
            TypeApplication(ref mut lhs, ref mut rhs) => {
                freshen_(env, subs, constraints, *lhs);
                freshen_(env, subs, constraints, *rhs);
                None
            }
            _ => None
        };
        match result {
            Some(x) => *typ = x,
            None => ()
        }
    }
    freshen_(env, subs, typ.constraints, &mut typ.value);
    for constraint in typ.constraints.mut_iter() {
        match subs.subs.find(&constraint.variables[0]) {
            Some(new) => constraint.variables[0] = new.var().clone(),
            None => ()
        }
    }
}
///Walks through a type and updates it with new type variables.
fn freshen_all(env: &mut TypeEnvironment, subs: &mut Substitution, typ: &mut Type) {
    let result = match typ {
        &TypeVariable(ref id) => freshen_var(env, subs, [], id),
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
///Updates the variable var, also making sure the constraints are updated appropriately
fn freshen_var(env: &mut TypeEnvironment, subs: &mut Substitution, constraints: &[Constraint], id: &TypeVariable) -> Option<Type> {
    subs.subs.find(id)
        .map(|var| var.clone())
        .or_else(|| {
        let mut new = env.new_var_kind(id.kind.clone());
        match new {
            TypeVariable(ref mut v) => v.age = id.age,
            _ => ()
        }
        subs.subs.insert(id.clone(), new.clone());
        {
            let mut constraints_for_id = constraints.iter()
                .filter(|c| c.variables[0] == *id);
            //Add all the constraints to he environment for the 'new' variable
            for c in constraints_for_id {
                env.insert_constraint(new.var(), c.class.clone());
            }
        }
        Some(new)
    })
}

///Takes two types and attempts to make them the same type
fn unify_location(env: &mut TypeEnvironment, subs: &mut Substitution, location: &Location, lhs: &mut Type, rhs: &mut Type) {
    debug!("{} Unifying {} <-> {}", location, *lhs, *rhs);
    match unify(env, subs, lhs, rhs) {
        Ok(()) => (),
        Err(error) => fail_type_error(location, lhs, rhs, error)
    }
}

fn fail_type_error(location: &Location, lhs: &Type, rhs: &Type, error: TypeError) -> ! {
    match error {
        UnifyFail(l, r) => fail!("{} Error: Could not unify types\n{}\nand\n{}\nin types\n{}\nand\n{}", location, l, r, *lhs, *rhs),
        RecursiveUnification => fail!("{} Error: Recursive unification between {}\nand\n{}", location, *lhs, *rhs),
        WrongArity(l, r) =>
            fail!("{} Error: Types do not have the same arity.\n{} <-> {}\n{} <-> {}\n{}\nand\n{}"
                , location, l, r, l.kind(), r.kind(), *lhs, *rhs),
        MissingInstance(class, typ, id) => fail!("{} Error: The instance {} {} was not found as required by {} when unifying {}\nand\n{}", location, class, typ, id, *lhs, *rhs)
    }
}

enum TypeError {
    UnifyFail(Type, Type),
    RecursiveUnification,
    WrongArity(Type, Type),
    MissingInstance(InternedStr, Type, TypeVariable)
}
///Tries to bind the type to the variable.
///Returns Ok if the binding was possible.
///Returns Error if the binding was not possible and the reason for the error.
fn bind_variable(env: &mut TypeEnvironment, subs: &mut Substitution, var: &TypeVariable, typ: &Type) -> Result<(), TypeError> {
    match *typ {
        TypeVariable(ref var2) => {
            if var != var2 {
                subs.subs.insert(var.clone(), typ.clone());
                for (_, v) in subs.subs.mut_iter() {
                    replace_var(v, var, typ);
                }
                match env.constraints.pop(var) {
                    Some(constraints) => {
                        for c in constraints.iter() {
                            env.insert_constraint(var2, c.clone());
                        }
                    }
                    None => ()
                }
            }
            Ok(())
        }
        _ => {
            if occurs(var, typ) {
                return Err(RecursiveUnification);
            }
            else if var.kind != *typ.kind() {
                return Err(WrongArity(TypeVariable(var.clone()), typ.clone()));
            }
            else {
                for (_, replaced) in subs.subs.mut_iter() {
                    replace_var(replaced, var, typ);
                }
                subs.subs.insert(var.clone(), typ.clone());
                match env.constraints.find(var) {
                    Some(constraints) => {
                        for c in constraints.iter() {
                            if !env.has_instance(*c, typ) {
                                match *typ {
                                    TypeConstructor(ref op) => {
                                        if *c == intern("Num") && (op.name == intern("Int") || op.name == intern("Double")) && *typ.kind() == star_kind {
                                            continue;
                                        }
                                        else if *c == intern("Fractional") && intern("Double") == op.name && *typ.kind() == star_kind {
                                            continue;
                                        }
                                    }
                                    _ => ()
                                }
                                return Err(MissingInstance(c.clone(), typ.clone(), var.clone()));
                            }
                        }
                    }
                    _ => ()
                }
                Ok(())
            }
        }
    }
}

///Tries to unify two types, updating the substition as well as the types directly with
///the new type values. 
fn unify(env: &mut TypeEnvironment, subs: &mut Substitution, lhs: &mut Type, rhs: &mut Type) -> Result<(), TypeError> {
    match (lhs, rhs) {
        (&TypeApplication(ref mut l1, ref mut r1), &TypeApplication(ref mut l2, ref mut r2)) => {
            unify(env, subs, *l1, *l2).and_then(|_| {
                replace(&mut env.constraints, *r1, subs);
                replace(&mut env.constraints, *r2, subs);
                unify(env, subs, *r1, *r2)
            })
        }
        (&TypeVariable(ref mut lhs), &TypeVariable(ref mut rhs)) => {
            //If both are variables we choose that they younger variable is replaced by the oldest
            //This is because when doing the quantifying, only variables that are created during
            //the inference of mutually recursive bindings should be quantified, but if a newly
            //created variable is unified with one from an outer scope we need to prefer the older
            //so that the variable does not get quantified
            if lhs.age > rhs.age {
                let x = bind_variable(env, subs, lhs, &TypeVariable(rhs.clone()));
                if x.is_ok() {
                    *lhs = rhs.clone();
                }
                x
            }
            else {
                let x = bind_variable(env, subs, rhs, &TypeVariable(lhs.clone()));
                if x.is_ok() {
                    *rhs = lhs.clone();
                }
                x
            }
        }
        (&TypeConstructor(ref lhs), &TypeConstructor(ref rhs)) =>
            if lhs.name == rhs.name { Ok(()) } else { Err(UnifyFail(TypeConstructor(lhs.clone()), TypeConstructor(rhs.clone()))) },
        (lhs, rhs) => {
            let x = match lhs {
                &TypeVariable(ref mut var) => bind_variable(env, subs, var, rhs),
                lhs => {
                    let y = match rhs {
                        &TypeVariable(ref mut var) => bind_variable(env, subs, var, lhs),
                        _ => return Err(UnifyFail(lhs.clone(), rhs.clone()))
                    };
                    if y.is_ok() {
                        *rhs = lhs.clone();
                    }
                    return y;
                }
            };
            if x.is_ok() {
                *lhs = rhs.clone();
            }
            x
        }
    }
}

fn match_or_fail(env: &mut TypeEnvironment, subs: &mut Substitution, location: &Location, lhs: &mut Type, rhs: &Type) {
    debug!("Match {} --> {}", *lhs, *rhs);
    match match_(env, subs, lhs, rhs) {
        Ok(()) => (),
        Err(error) => fail_type_error(location, lhs, rhs, error)
    }
}
///Match performs matching which is walks through the same process as unify but only allows
///the updates to be one way (such as between a type and the type in a type signature).
fn match_(env: &mut TypeEnvironment, subs: &mut Substitution, lhs: &mut Type, rhs: &Type) -> Result<(), TypeError> {
    match (lhs, rhs) {
        (&TypeApplication(ref mut l1, ref mut r1), &TypeApplication(ref l2, ref r2)) => {
            match_(env, subs, *l1, *l2).and_then(|_| {
                replace(&mut env.constraints, *r1, subs);
                match_(env, subs, *r1, *r2)
            })
        }
        (&TypeVariable(ref mut lhs), &TypeVariable(ref rhs)) => {
            let x = bind_variable(env, subs, lhs, &TypeVariable(rhs.clone()));
            *lhs = rhs.clone();
            x
        }
        (&TypeConstructor(ref lhs), &TypeConstructor(ref rhs)) =>
            if lhs.name == rhs.name { Ok(()) } else { Err(UnifyFail(TypeConstructor(lhs.clone()), TypeConstructor(rhs.clone()))) },
        (lhs, rhs) => {
            let x = match lhs {
                &TypeVariable(ref mut var) => bind_variable(env, subs, var, rhs),
                _ => return Err(UnifyFail(lhs.clone(), rhs.clone()))
            };
            *lhs = rhs.clone();
            x
        }
    }
}


///Creates a graph containing a vertex for each binding and edges from every binding to every other
///binding that it references
fn build_graph(bindings: &Bindings) -> Graph<(uint, uint)> {
    let mut graph = Graph::new();
    let mut map = HashMap::new();
    bindings.each_binding(|binds, i| {
        let index = graph.new_vertex(i);
        map.insert(binds[0].name.clone(), index);
    });
    bindings.each_binding(|binds, _| {
        for bind in binds.iter() {
            match bind.matches {
                Simple(ref e) => add_edges(&mut graph, &map, *map.get(&bind.name), e),
                Guards(ref gs) => {
                    for g in gs.iter() {
                        add_edges(&mut graph, &map, *map.get(&bind.name), &g.predicate);
                        add_edges(&mut graph, &map, *map.get(&bind.name), &g.expression);
                    }
                }
            }
        }
    });
    graph
}

///Adds an edge for each identifier which refers to a binding in the graph
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

///Walks through the type and calls the functions on each variable and type constructor
fn each_type(typ: &Type, mut var_fn: |&TypeVariable|, mut op_fn: |&TypeConstructor|) {
    each_type_(typ, &mut var_fn, &mut op_fn);
}
fn each_type_(typ: &Type, var_fn: &mut |&TypeVariable|, op_fn: &mut |&TypeConstructor|) {
    match typ {
        &TypeVariable(ref var) => (*var_fn)(var),
        &TypeConstructor(ref op) => (*op_fn)(op),
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

///Takes a function type and calls the 'func' with the argument to the function and its
///return type.
///Returns true if the function was called.
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
pub fn op_apply(lhs: TypedExpr, op: InternedStr, rhs: TypedExpr) -> TypedExpr {
    TypedExpr::new(OpApply(box lhs, op, box rhs))
}
#[cfg(test)]
pub fn let_(bindings : ~[Binding], expr : TypedExpr) -> TypedExpr {
    TypedExpr::new(Let(bindings, box expr))
}
#[cfg(test)]
pub fn case(expr : TypedExpr, alts: ~[Alternative]) -> TypedExpr {
    TypedExpr::new(Case(box expr, alts))
}
#[cfg(test)]
pub fn paren(expr : TypedExpr) -> TypedExpr {
    TypedExpr::new(Paren(box expr))
}

pub fn typecheck_string(module: &str) -> IoResult<Vec<Module<Name>>> {
    use parser::parse_string;
    use renamer::rename_modules;
    let mut modules = rename_modules(try!(parse_string(module)));
    let mut env = TypeEnvironment::new();
    for module in modules.mut_iter() {
        env.typecheck_module(module);
    }
    Ok(modules)
}

///Parses a module, renames and typechecks it, as well as all of its imported modules
pub fn typecheck_module(module: &str) -> IoResult<Vec<Module<Name>>> {
    use parser::parse_modules;
    use renamer::rename_modules;
    use infix::PrecedenceVisitor;
    let mut modules = rename_modules(try!(parse_modules(module)));
    let mut prec_visitor = PrecedenceVisitor::new();
    for module in modules.mut_iter() {
        prec_visitor.visit_module(module);
    }
    let mut env = TypeEnvironment::new();
    for module in modules.mut_iter() {
        env.typecheck_module(module);
    }
    Ok(modules)
}


#[cfg(test)]
pub mod test {
use interner::*;
use module::*;
use typecheck::*;
use renamer::*;

use parser::Parser;
use std::io::File;

use test::Bencher;

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
    let e = let_(~[Binding { arguments: ~[], name: intern("test"), matches: Simple(unary_bind), typ: Default::default() }], identifier("test"));
    let mut expr = rename_expr(e);
    env.typecheck_expr(&mut expr);

    assert_eq!(expr.typ, unary_func);
}

#[test]
fn typecheck_case() {
    let mut env = TypeEnvironment::new();
    let type_int = int_type();

    let mut parser = Parser::new(r"case [] of { x:xs -> primIntAdd x 2 ; [] -> 3}".chars());
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
    x:xs -> x
    [] -> 10";
    let module = do_typecheck(file);

    assert_eq!(module.bindings[1].typ.value, int_type());
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

    let typ = function_type_(Type::new_var(intern("a")), bool_type());
    let bind_type0 = module.bindings[0].typ.value;
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
            assert_eq!(binds[0].typ.value, int_type);
            assert_eq!(binds[1].name.as_slice(), "test");
            assert_eq!(binds[1].typ.value, list_type);
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

    let typ = &module.bindings[0].typ.value;
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

    let typ = &module.bindings[0].typ;
    let a = Type::new_var(intern("a"));
    let b = Type::new_var(intern("b"));
    let test = function_type_(a.clone(), function_type_(b.clone(), int_type()));
    assert_eq!(&typ.value, &test);
    assert_eq!(typ.constraints[0].class, intern("Test"));
    assert_eq!(typ.constraints[1].class, intern("Test"));
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
fn typecheck_super_class() {
    let mut parser = Parser::new(
r"data Bool = True | False

class Eq a where
    (==) :: a -> a -> Bool

class Eq a => Ord a where
    (<) :: a -> a -> Bool

instance Eq Bool where
    (==) True True = True
    (==) False False = True
    (==) _ _ = False

instance Ord Bool where
    (<) False True = True
    (<) _ _ = False

test x y = case x < y of
    True -> True
    False -> x == y

".chars());

    let mut module = rename_module(parser.module());

    let mut env = TypeEnvironment::new();
    env.typecheck_module(&mut module);

    let typ = &module.bindings[0].typ;
    let a = Type::new_var(intern("a"));
    assert_eq!(typ.value, function_type_(a.clone(), function_type_(a.clone(), bool_type())));
    assert_eq!(typ.constraints.len(), 1);
    assert_eq!(typ.constraints[0].class, intern("Ord"));
}

#[test]
#[should_fail]
fn typecheck_missing_super_class() {
    let mut parser = Parser::new(
r"data Bool = True | False

class Eq a where
    (==) :: a -> a -> Bool

class Eq a => Ord a where
    (<) :: a -> a -> Bool

instance Ord Bool where
    (<) False True = True
    (<) _ _ = False

test y = False < y

".chars());

    let mut module = rename_module(parser.module());

    let mut env = TypeEnvironment::new();
    env.typecheck_module(&mut module);
}

#[test]
fn typecheck_instance_super_class() {
    let mut parser = Parser::new(
r"data Bool = True | False

class Eq a where
    (==) :: a -> a -> Bool

instance Eq a => Eq [a] where
    (==) xs ys = case xs of
        x2:xs2 -> case ys of
            y2:ys2 -> (x2 == y2) && (xs2 == ys2)
            [] -> False
        [] -> case ys of
            y2:ys2 -> False
            [] -> True

(&&) :: Bool -> Bool -> Bool
(&&) x y = case x of
    True -> y
    False -> False
".chars());

    let mut module = rename_module(parser.module());

    let mut env = TypeEnvironment::new();
    env.typecheck_module(&mut module);

    let typ = &module.instances[0].bindings[0].typ;
    let list_type = list_type(Type::new_var(intern("a")));
    assert_eq!(typ.value, function_type_(list_type.clone(), function_type_(list_type, bool_type())));
    let var = typ.value.appl().appr().appr().var();
    assert_eq!(typ.constraints, box [Constraint { class: intern("Eq"), variables: box [var.clone()] }]);
}

#[test]
fn typecheck_num_double() {

    let file = 
r"test x = primDoubleAdd 0 x";
    let module = do_typecheck(file);

    let typ = function_type_(double_type(), double_type());
    let bind_type0 = module.bindings[0].typ.value;
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
    assert_eq!(main.typ.value, Type::new_op(intern("Maybe"), ~[int_type()]));
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
    assert_eq!(id_bind.typ.value, function_type_(Type::new_var(intern("a")), Type::new_var(intern("a"))));
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
    assert_eq!(module.bindings[0].typ.value, list_type(bool_type()));
    assert_eq!(module.bindings[1].name.as_slice(), "test2");
    assert_eq!(module.bindings[1].typ.value, int_type());
}

#[test]
fn type_declaration() {
    
    let input =
r"
class Test a where
    test :: a -> Int

instance Test Int where
    test x = x

test2 :: Test a => a -> Int -> Int
test2 x y = primIntAdd (test x) y";
    let module = do_typecheck(input);

    assert_eq!(module.bindings[0].typ, module.typeDeclarations[0].typ);
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
    let z = [1::Int]
        y = reverse x
        t = [2::Int]
    putStrLn y
";
    let module = do_typecheck_with(file, [&prelude as &DataTypes]);

    assert_eq!(module.bindings[0].typ.value, function_type_(list_type(char_type()), io(unit())));
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
    y:ys <- x
    return y
";
    let module = do_typecheck_with(file, [&prelude as &DataTypes]);

    let var = Type::new_var(intern("a"));
    let t = function_type_(Type::new_var_args(intern("c"), ~[list_type(var.clone())]), Type::new_var_args(intern("c"), ~[var.clone()]));
    assert_eq!(module.bindings[0].typ.value, t);
    assert_eq!(module.bindings[0].typ.constraints[0].class, intern("Monad"));
}

#[test]
fn binding_pattern() {
    let module = do_typecheck(r"
test f (x:xs) = f x : test f xs
test _ [] = []
");
    let a = Type::new_var(intern("a"));
    let b = Type::new_var(intern("b"));
    let test = function_type_(function_type_(a.clone(), b.clone()), function_type_(list_type(a), list_type(b)));
    assert_eq!(module.bindings[0].typ.value, test);
}

#[test]
fn guards() {
    let module = do_typecheck(r"

data Bool = True | False

if_ p x y
    | p = x
    | True = y
");
    let var = Type::new_var(intern("a"));
    let test = function_type_(bool_type()
             , function_type_(var.clone()
             , function_type_(var.clone(),
                              var.clone())));
    assert_eq!(module.bindings[0].typ.value, test);
}

#[test]
fn typedeclaration_on_expression() {
    let module = do_typecheck(r"
test = [1,2,3 :: Int]
");
    assert_eq!(module.bindings[0].typ.value, list_type(int_type()));
}

#[test]
#[should_fail]
fn typedeclaration_to_general() {
    do_typecheck(r"
test x = primIntAdd 2 x :: Num a => a
");
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
