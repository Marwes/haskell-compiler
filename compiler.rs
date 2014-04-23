use core::*;
use typecheck::{Types, TypeEnvironment, function_type};
use scoped_map::ScopedMap;
use std::iter::range_step;
use std::default::Default;

use core::translate::{translate_module};
use lambda_lift::do_lambda_lift;

#[deriving(Eq, Clone, Show)]
pub enum Instruction {
    Add,
    Sub,
    Multiply,
    Divide,
    Remainder,
    IntEQ,
    IntLT,
    IntLE,
    IntGT,
    IntGE,
    DoubleAdd,
    DoubleSub,
    DoubleMultiply,
    DoubleDivide,
    DoubleRemainder,
    DoubleEQ,
    DoubleLT,
    DoubleLE,
    DoubleGT,
    DoubleGE,
    IntToDouble,
    DoubleToInt,
    Push(uint),
    PushGlobal(uint),
    PushInt(int),
    PushFloat(f64),
    PushChar(char),
    Mkap,
    Eval,
    Unwind,
    Update(uint),
    Pop(uint),
    Slide(uint),
    Split(uint),
    Pack(u16, u16),
    CaseJump(uint),
    Jump(uint),
    JumpFalse(uint),
    PushDictionary(uint),
    PushDictionaryMember(uint),
}
enum Var<'a> {
    StackVariable(uint),
    GlobalVariable(uint),
    ConstructorVariable(u16, u16),
    ClassVariable(&'a Type, &'a TypeVariable),
    ConstraintVariable(uint, &'a Type, &'a[Constraint])
}

impl <'a> Clone for Var<'a> {
    fn clone(&self) -> Var<'a> {
        match self {
            &StackVariable(x) => StackVariable(x),
            &GlobalVariable(x) => GlobalVariable(x),
            &ConstructorVariable(x, y) => ConstructorVariable(x, y),
            &ClassVariable(x, y) => ClassVariable(x, y),
            &ConstraintVariable(x, y, z) => ConstraintVariable(x, y, z)
        }
    }
}

pub struct SuperCombinator {
    pub arity : uint,
    pub name: Name,
    pub assembly_id: uint,
    pub instructions : ~[Instruction],
    pub type_declaration: TypeDeclaration,
    pub constraints: ~[Constraint]
}
impl SuperCombinator {
    fn new() -> SuperCombinator {
        SuperCombinator { arity : 0, name: Name { name: ~"", uid: 0}, instructions : ~[], type_declaration: Default::default(), constraints: ~[], assembly_id: 0 }
    }
}

pub struct Assembly {
    pub superCombinators: ~[SuperCombinator],
    pub instance_dictionaries: ~[~[uint]],
    pub classes: ~[Class],
    pub instances: ~[(~[Constraint], Type)],
    pub data_definitions: ~[DataDefinition],
    pub offset: uint
}

trait Globals {
    ///Lookup a global variable
    fn find_global<'a>(&'a self, name: &Name) -> Option<Var<'a>>;
    fn find_constructor(&self, name: &str) -> Option<(u16, u16)>;
}

impl Globals for Assembly {
    fn find_global<'a>(&'a self, name: &Name) -> Option<Var<'a>> {
        let mut index = 0;
        for sc in self.superCombinators.iter() {
            if *name == sc.name {
                if sc.constraints.len() > 0 {
                    return Some(ConstraintVariable(self.offset + index, &sc.type_declaration.typ, sc.constraints));
                }
                else {
                    return Some(GlobalVariable(self.offset + index));
                }
            }
            index += 1;
        }
        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                if decl.name == name.name {
                    return Some(ClassVariable(&decl.typ, &class.variable));
                }
            }
        }
        
        self.find_constructor(name.name).map(|(tag, arity)| ConstructorVariable(tag, arity))
    }
    fn find_constructor(&self, name: &str) -> Option<(u16, u16)> {
        for data_def in self.data_definitions.iter() {
            for ctor in data_def.constructors.iter() {
                if name == ctor.name {
                    return Some((ctor.tag as u16, ctor.arity as u16));
                }
            }
        }
        None
    }
}

fn find_global<'a>(module: &'a Module<Id>, offset: uint, name: &Name) -> Option<Var<'a>> {
    
    for class in module.classes.iter() {
        for decl in class.declarations.iter() {
            if decl.name == name.name {
                return Some(ClassVariable(&decl.typ, &class.variable));
            }
        }
    }

    let mut global_index = 0;
    for bind in module.bindings.iter() {
        if bind.name.name == *name {
            let typ = bind.expression.get_type();
            let constraints = &bind.name.constraints;
            if constraints.len() > 0 {
                return Some(ConstraintVariable(offset + global_index, typ, *constraints));
            }
            else {
                return Some(GlobalVariable(offset + global_index));
            }
        }
        global_index += 1;
    }
    find_constructor(module, name.name).map(|(tag, arity)| ConstructorVariable(tag, arity))
}

fn find_constructor(module: &Module<Id>, name: &str) -> Option<(u16, u16)> {

    for dataDef in module.data_definitions.iter() {
        for ctor in dataDef.constructors.iter() {
            if name == ctor.name {
                return Some((ctor.tag as u16, ctor.arity as u16));
            }
        }
    }
    None
}

impl Types for Module<Id> {
    fn find_type<'a>(&'a self, name: &str) -> Option<&'a Type> {
        for bind in self.bindings.iter() {
            if bind.name.name.name.equiv(&name) {
                return Some(bind.expression.get_type());
            }
        }

        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                if decl.name.equiv(&name) {
                    return Some(&decl.typ);
                }
            }
        }
        for data in self.data_definitions.iter() {
            for ctor in data.constructors.iter() {
                if ctor.name.equiv(&name) {
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
        for &(ref constraints, ref op) in self.instances.iter() {
            match op {
                &TypeApplication(ref op, ref t) => {
                    if classname == extract_applied_type(*op).op().name && extract_applied_type(*t).op().name == extract_applied_type(typ).op().name {
                        let c : &[Constraint] = *constraints;
                        let o : &Type = *op;
                        return Some((c, o));
                    }
                }
                _ => ()
            }
        }
        None
    }

    fn each_constraint_list(&self, func: |&[Constraint]|) {
        for bind in self.bindings.iter() {
            func(bind.name.constraints);
        }

        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                func(decl.context);
            }
        }
    }
}

fn extract_applied_type<'a>(typ: &'a Type) -> &'a Type {
    match typ {
        &TypeApplication(ref lhs, _) => extract_applied_type(*lhs),
        _ => typ
    }
}

impl Types for Assembly {
    ///Lookup a type
    fn find_type<'a>(&'a self, name: &str) -> Option<&'a Type> {
        for sc in self.superCombinators.iter() {
            if sc.name.name.equiv(&name) {
                return Some(&sc.type_declaration.typ);
            }
        }
        
        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                if name == decl.name {
                    return Some(&decl.typ);
                }
            }
        }

        for data_def in self.data_definitions.iter() {
            for ctor in data_def.constructors.iter() {
                if name == ctor.name {
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
        for &(ref constraints, ref op) in self.instances.iter() {
            match op {
                &TypeApplication(ref op, ref t) => {
                    if classname == extract_applied_type(*op).op().name && extract_applied_type(*t).op().name == extract_applied_type(typ).op().name {
                        let c : &[Constraint] = *constraints;
                        let o : &Type = *op;
                        return Some((c, o));
                    }
                }
                _ => ()
            }
        }
        None
    }
    fn each_constraint_list(&self, func: |&[Constraint]|) {
        for sc in self.superCombinators.iter() {
            func(sc.constraints);
        }
        
        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                func(decl.context);
            }
        }
    }
}

pub struct Compiler<'a> {
    pub type_env: &'a TypeEnvironment<'a>,
    ///Hashmap containging class names mapped to the functions it contains
    pub instance_dictionaries: Vec<(~[(~str, Type)], ~[uint])>,
    pub stackSize : uint,
    ///Array of all the assemblies which can be used to lookup functions in
    pub assemblies: Vec<&'a Assembly>,
    module: Option<&'a Module<Id>>,
    variables: ScopedMap<Name, Var<'a>>
}


impl <'a> Compiler<'a> {
    pub fn new(type_env: &'a TypeEnvironment) -> Compiler<'a> {
        Compiler { type_env: type_env, instance_dictionaries: Vec::new(),
            stackSize : 0, assemblies: Vec::new(),
            module: None,
            variables: ScopedMap::new()
        }
    }
    
    pub fn compileModule(&mut self, module : &'a Module<Id>) -> Assembly {
        self.module = Some(module);
        let mut superCombinators = Vec::new();
        let mut instance_dictionaries = Vec::new();
        let mut data_definitions = Vec::new();
        
        for def in module.data_definitions.iter() {
            let mut constructors = Vec::new();
            for ctor in def.constructors.iter() {
                constructors.push(ctor.clone());
            }
            data_definitions.push(def.clone());
        }

        for bind in module.bindings.iter() {
            let mut sc = self.compileBinding(bind);
            let constraints = self.type_env.find_constraints(bind.expression.get_type());
            sc.constraints = constraints;
            sc.name = bind.name.name.clone();
            superCombinators.push(sc);
        }

        for &(_, ref dict) in self.instance_dictionaries.iter() {
            instance_dictionaries.push(dict.clone());
        }
        self.module = None;
        Assembly {
            superCombinators: superCombinators.move_iter().collect(),
            instance_dictionaries: instance_dictionaries.move_iter().collect(),
            offset: self.assemblies.iter().flat_map(|assembly| assembly.superCombinators.iter()).len(),
            classes: module.classes.clone(),
            instances: module.instances.iter().map(|x| x.clone()).collect(),
            data_definitions: data_definitions.move_iter().collect()
        }
    }

    fn compileBinding(&mut self, bind : &Binding<Id>) -> SuperCombinator {
        fn arity(expr: &Expr<Id>) -> uint {
            match expr {
                &Lambda(_, ref body) => 1 + arity(*body),
                _ => 0
            }
        }
        debug!("Compiling binding {}", bind.name);
        let mut comb = SuperCombinator::new();
        comb.assembly_id = self.assemblies.len();
        comb.type_declaration = TypeDeclaration {
            name: bind.name.name.name.clone(),
            typ: bind.name.typ.clone(),
            context: bind.name.constraints.clone()
        };
        comb.constraints = bind.name.constraints.clone();
        let dict_arg = if bind.name.constraints.len() > 0 { 1 } else { 0 };
        comb.arity = arity(&bind.expression) + dict_arg;
        let mut instructions = Vec::new();
        self.scope(|this| {
            if dict_arg == 1 {
                this.newStackVar(Name { name: ~"$dict", uid: 0 });
            }
            debug!("{}\n {}", bind.name, bind.expression);
            match &bind.expression {
                &Lambda(_, _) => {
                    this.compile(&bind.expression, &mut instructions, true);
                    instructions.push(Update(0));
                    instructions.push(Pop(comb.arity));
                    instructions.push(Unwind);
                }
                _ => {
                    this.compile(&bind.expression, &mut instructions, true);
                    instructions.push(Update(0));
                    instructions.push(Unwind);
                }
            }
        });
        comb.instructions = instructions.move_iter().collect();
        comb
    }
    
    ///Find a variable by walking through the stack followed by all globals
    fn find<'r>(&'r self, identifier : &Name) -> Option<Var<'r>> {
        self.variables.find(identifier).map(|x| x.clone())
        .or_else(|| {
            match self.module {
                Some(ref module) => {
                    let n = self.assemblies.len();
                    let offset = if n > 0 {
                        let assembly = self.assemblies.get(n-1);
                        assembly.offset + assembly.superCombinators.len()
                    }
                    else {
                        0
                    };
                    find_global(*module, offset, identifier)
                }
                None => None
            }
        })
        .or_else(|| {
            for assembly in self.assemblies.iter() {
                match assembly.find_global(identifier) {
                    Some(var) => return Some(var),
                    None => ()
                }
            }
            None
        }).or_else(|| {
            let identifier = identifier.name.as_slice();
            if identifier.len() >= 3 && identifier.char_at(0) == '('
            && identifier.char_at(identifier.len() - 1) == ')'
            && identifier.chars().skip(1).take(identifier.len() - 2).all(|c| c == ',') {
                return Some(ConstructorVariable(0, (identifier.len() - 1) as u16));
            }
            match identifier {
                &"[]" => Some(ConstructorVariable(0, 0)),
                &":" => Some(ConstructorVariable(1, 2)),
                _ => None
            }
        })
    }

    fn find_constructor(&self, identifier : &str) -> Option<(u16, u16)> {
        self.module.and_then(|module| find_constructor(module, identifier))
        .or_else(|| {
            for assembly in self.assemblies.iter() {
                match assembly.find_constructor(identifier) {
                    Some(var) => return Some(var),
                    None => ()
                }
            }
            None
        }).or_else(|| {
            if identifier.len() >= 3 && identifier.char_at(0) == '('
            && identifier.char_at(identifier.len() - 1) == ')'
            && identifier.chars().skip(1).take(identifier.len() - 2).all(|c| c == ',') {
                return Some((0, (identifier.len() - 1) as u16));
            }
            match identifier {
                &"[]" => Some((0, 0)),
                &":" => Some((1, 2)),
                _ => None
            }
        })
    }

    fn find_class<'r>(&'r self, name: &str) -> Option<&'r Class> {
        self.module.and_then(|m| m.find_class(name))
            .or_else(|| {
            for types in self.assemblies.iter() {
                match types.find_class(name) {
                    Some(result) => return Some(result),
                    None => ()
                }
            }
            None
        })
    }

    fn newStackVar(&mut self, identifier : Name) {
        self.variables.insert(identifier, StackVariable(self.stackSize));
        self.stackSize += 1;
    }

    fn scope(&mut self, f: |&mut Compiler|) {
        self.variables.enter_scope();
        let stackSize = self.stackSize;
        f(self);
        self.stackSize = stackSize;
        self.variables.exit_scope();
    }

    ///Compile an expression by appending instructions to the instructions array
    fn compile(&mut self, expr : &Expr<Id>, instructions : &mut Vec<Instruction>, strict: bool) {
        match expr {
            &Identifier(ref name) => {
                //When compiling a variable which has constraints a new instance dictionary
                //might be created which is returned here and added to the assembly
                let maybe_new_dict = match self.find(&name.name) {
                    None => fail!("Error: Undefined variable {}", *name),
                    Some(var) => {
                        match var {
                            StackVariable(index) => { instructions.push(Push(index)); None }
                            GlobalVariable(index) => { instructions.push(PushGlobal(index)); None }
                            ConstructorVariable(tag, arity) => { instructions.push(Pack(tag, arity)); None }
                            ClassVariable(typ, var) => self.compile_instance_variable(expr.get_type(), instructions, name.name.name, typ, var),
                            ConstraintVariable(index, _, constraints) => {
                                let x = self.compile_with_constraints(name.name.name, expr.get_type(), constraints, instructions);
                                instructions.push(PushGlobal(index));
                                instructions.push(Mkap);
                                x
                            }
                        }
                    }
                };
                match maybe_new_dict {
                    Some(dict) => self.instance_dictionaries.push(dict),
                    None => ()
                }
                if strict {
                    instructions.push(Eval);
                }
            }
            &Literal(ref literal) => {
                match &literal.value {
                    &Integral(i) => {
                        if literal.typ == Type::new_op(~"Int", ~[]) {
                            instructions.push(PushInt(i));
                        }
                        else if literal.typ == Type::new_op(~"Double", ~[]) {
                            instructions.push(PushFloat(i as f64));
                        }
                        else {
                            let fromInteger = Identifier(Id {
                                name: Name { name: ~"fromInteger", uid: 999999 }, 
                                typ: function_type(&Type::new_op(~"Int", ~[]), &literal.typ),
                                constraints: ~[]
                            });
                            let number = Literal(Literal { typ: Type::new_op(~"Double", ~[]), value: Integral(i) });
                            let apply = Apply(~fromInteger, ~number);
                            self.compile(&apply, instructions, strict);
                        }
                    }
                    &Fractional(f) => {
                        if literal.typ == Type::new_op(~"Double", ~[]) {
                            instructions.push(PushFloat(f));
                        }
                        else {
                            let fromRational = Identifier(Id {
                                name: Name { name: ~"fromRational", uid: 999999 }, 
                                typ: function_type(&Type::new_op(~"Double", ~[]), &literal.typ),
                                constraints: ~[]
                            });
                            let number = Literal(Literal {
                                typ: Type::new_op(~"Double", ~[]),
                                value: Fractional(f)
                            });
                            let apply = Apply(~fromRational, ~number);
                            self.compile(&apply, instructions, strict);
                        }
                    }
                    &String(ref s) => {
                        instructions.push(Pack(0, 0));
                        for c in s.chars_rev() {
                            instructions.push(PushChar(c));
                            instructions.push(Pack(1, 2));
                        }
                    }
                    &Char(c) => instructions.push(PushChar(c))
                }
            }
            &Apply(ref func, ref arg) => {
                if !self.primitive(*func, *arg, instructions) {
                    self.compile(*arg, instructions, false);
                    self.compile(*func, instructions, false);
                    match instructions.get(instructions.len() - 1) {
                        &Pack(_, _) => (),//The application was a constructor so dont do Mkap and the Pack instruction is strict already
                        _ => {
                            instructions.push(Mkap);
                            if strict {
                                instructions.push(Eval);
                            }
                        }
                    }
                }
            }
            &Lambda(ref varname, ref body) => {
                self.scope(|this| {
                    this.newStackVar(varname.name.clone());
                    this.compile(*body, instructions, false);
                });
            }
            &Let(ref bindings, ref body) => {
                for bind in bindings.iter() {
                    self.newStackVar(bind.name.name.clone());
                    self.compile(&bind.expression, instructions, false);
                }
                self.compile(*body, instructions, strict);
                instructions.push(Slide(bindings.len()));
            }
            &Case(ref body, ref alternatives) => {
                self.compile(*body, instructions, true);
                self.stackSize += 1;//Dummy variable for the case expression
                //Storage for all the jumps that should go to the end of the case expression
                let mut end_branches = Vec::new();
                for i in range(0, alternatives.len()) {
                    let alt = &alternatives[i];

                    self.scope(|this| {
                        let pattern_start = instructions.len() as int;
                        let mut branches = Vec::new();
                        let stack_increase = this.compile_pattern(&alt.pattern, &mut branches, instructions, this.stackSize - 1, 0);
                        let pattern_end = instructions.len() as int;

                        this.compile(&alt.expression, instructions, strict);
                        instructions.push(Slide(stack_increase));
                        instructions.push(Jump(0));//Should jump to the end
                        end_branches.push(instructions.len() - 1);

                        //Here the current branch ends and the next one starts
                        //We need to set all the jump instructions to their actual location
                        //and append Slide instructions to bring the stack back to normal if the match fails
                        for j in range_step(pattern_end, pattern_start, -1) {
                            match *instructions.get(j as uint) {
                                Jump(_) => {
                                    *instructions.get_mut(j as uint) = Jump(instructions.len());
                                }
                                JumpFalse(_) => *instructions.get_mut(j as uint) = JumpFalse(instructions.len()),
                                Split(size) => instructions.push(Pop(size)),
                                _ => ()
                            }
                        }
                    });
                }
                self.stackSize -= 1;
                for branch in end_branches.iter() {
                    *instructions.get_mut(*branch) = Jump(instructions.len());
                }
                //Remove the matched expr
                instructions.push(Slide(1));
                if strict {
                    instructions.push(Eval);
                }
            }
        }
    }

    ///Compile a function which is defined in a class
    fn compile_instance_variable(&self, actual_type: &Type, instructions: &mut Vec<Instruction>, name: &str, typ: &Type, var: &TypeVariable) -> Option<(~[(~str, Type)], ~[uint])> {
        match try_find_instance_type(var, typ, actual_type) {
            Some(typename) => {
                //We should be able to retrieve the instance directly
                let instance_fn_name = "#" + typename + name;
                let name = Name {name: instance_fn_name, uid: 0 };
                match self.find(&name) {
                    Some(GlobalVariable(index)) => {
                        instructions.push(PushGlobal(index));
                        None
                    }
                    Some(ConstraintVariable(index, _function_type, constraints)) => {
                        let dict = self.compile_with_constraints(name.name, actual_type, constraints, instructions);
                        instructions.push(PushGlobal(index));
                        instructions.push(Mkap);
                        dict
                    }
                    _ => fail!("Unregistered instance function {}", name)
                }
            }
            None => {
                let constraints = self.type_env.find_constraints(actual_type);
                self.compile_with_constraints(name, actual_type, constraints, instructions)
            }
        }
    }

    ///Compile the loading of a variable which has constraints and will thus need to load a dictionary with functions as well
    fn compile_with_constraints(&self, name: &str, typ: &Type, constraints: &[Constraint], instructions: &mut Vec<Instruction>) -> Option<(~[(~str, Type)], ~[uint])> {
        match self.find(&Name { name: "$dict".to_owned(), uid: 0}) {
            Some(StackVariable(_)) => {
                //Push dictionary or member of dictionary
                match self.push_dictionary_member(constraints, name) {
                    Some(index) => instructions.push(PushDictionaryMember(index)),
                    None => instructions.push(Push(0))
                }
                None
            }
            _ => {
                //get dictionary index
                //push dictionary
                let dictionary_key = self.type_env.find_specialized_instances(name, typ);
                let (index, dict) = self.find_dictionary_index(dictionary_key);
                instructions.push(PushDictionary(index));
                dict
            }
        }
    }

    ///Lookup which index in the instance dictionary that holds the function called 'name'
    fn push_dictionary_member(&self, constraints: &[Constraint], name: &str) -> Option<uint> {
        if constraints.len() == 0 {
            fail!("Attempted to push dictionary member '{}' with no constraints", name)
        }
        for c in constraints.iter() {
            match self.find_class(c.class) {
                Some(class) => {
                    for ii in range(0, class.declarations.len()) {
                        if class.declarations[ii].name.equiv(&name) {
                            return Some(ii)
                        }
                    }
                }
                None => fail!("Undefined instance {:?}", c)
            }
        }
        None
    }

    ///Find the index of the instance dictionary for the constraints and types in 'constraints'
    ///Returns the index and possibly a new dictionary which needs to be added to the assemblies dictionaries
    fn find_dictionary_index(&self, constraints: &[(~str, Type)]) -> (uint, Option<(~[(~str, Type)], ~[uint])>) {


        fn extract_applied_type<'a>(typ: &'a Type) -> &'a Type {
            match typ {
                &TypeApplication(ref lhs, _) => extract_applied_type(*lhs),
                _ => typ
            }
        }

        let dict_len = self.instance_dictionaries.len();
        for ii in range(0, dict_len) {
            if self.instance_dictionaries.get(ii).ref0().equiv(&constraints) {
                return (ii, None);
            }
        }

        if constraints.len() == 0 {
            fail!("Error: Attempted to compile dictionary with no constraints at <unknown>");
        }
        let mut function_indexes = Vec::new();
        for &(ref class_name, ref typ) in constraints.iter() {
            match self.find_class(*class_name) {
                Some(class) => {
                    assert!(class.declarations.len() > 0);
                    for decl in class.declarations.iter() {
                        let f = "#" + extract_applied_type(typ).op().name + decl.name;
                        let name = Name { name: f, uid: 0 };
                        match self.find(&name) {
                            Some(GlobalVariable(index)) => {
                                function_indexes.push(index as uint);
                            }
                            _ => fail!("Did not find function {}", name)
                        }
                    }
                }
                None => fail!("Could not find class '{}'", *class_name)
            }
        }
        (dict_len, Some((constraints.to_owned(), function_indexes.move_iter().collect())))
    }

    ///Attempt to compile a binary primitive, returning true if it succeded
    fn primitive(&mut self, func: &Expr<Id>, arg: &Expr<Id>, instructions: &mut Vec<Instruction>) -> bool {
        match func {
            &Apply(ref prim_func, ref arg2) => {
                let p: &Expr<Id> = *prim_func;
                match p {
                    &Identifier(ref name) => {
                        //Binary functions
                        let maybeOP = match name.name.name.as_slice() {
                            "primIntAdd" => Some(Add),
                            "primIntSubtract" => Some(Sub),
                            "primIntMultiply" => Some(Multiply),
                            "primIntDivide" => Some(Divide),
                            "primIntRemainder" => Some(Remainder),
                            "primIntEQ" => Some(IntEQ),
                            "primIntLT" => Some(IntLT),
                            "primIntLE" => Some(IntLE),
                            "primIntGT" => Some(IntGT),
                            "primIntGE" => Some(IntGE),
                            "primDoubleAdd" => Some(DoubleAdd),
                            "primDoubleSubtract" => Some(DoubleSub),
                            "primDoubleMultiply" => Some(DoubleMultiply),
                            "primDoubleDivide" => Some(DoubleDivide),
                            "primDoubleRemainder" => Some(DoubleRemainder),
                            "primDoubleEQ" => Some(DoubleEQ),
                            "primDoubleLT" => Some(DoubleLT),
                            "primDoubleLE" => Some(DoubleLE),
                            "primDoubleGT" => Some(DoubleGT),
                            "primDoubleGE" => Some(DoubleGE),
                            _ => None
                        };
                        match maybeOP {
                            Some(op) => {
                                self.compile(arg, instructions, true);
                                self.compile(*arg2, instructions, true);
                                instructions.push(op);
                                true
                            }
                            None => false
                        }
                    }
                    _ => false
                }
            }
            &Identifier(ref name) => {
                let n: &str = name.name.name;
                let maybeOP = match n {
                    "primIntToDouble" => Some(IntToDouble),
                    "primDoubleToInt" => Some(DoubleToInt),
                    _ => None
                };
                match maybeOP {
                    Some(op) => {
                        self.compile(arg, instructions, true);
                        instructions.push(op);
                        true
                    }
                    None => false
                }
            }
            _ => false
        }
    }

    fn compile_pattern(&mut self, pattern: &Pattern<Id>, branches: &mut Vec<uint>, instructions: &mut Vec<Instruction>, stack_index: uint, pattern_index: uint) -> uint {
        //TODO this is unlikely to work with nested patterns currently
        match pattern {
            &ConstructorPattern(ref name, ref patterns) => {
                instructions.push(Push(stack_index - pattern_index));
                match self.find_constructor(*name) {
                    Some((tag, _)) => {
                        instructions.push(CaseJump(tag as uint));
                        branches.push(instructions.len());
                        instructions.push(Jump(0));
                    }
                    _ => fail!("Undefined constructor {}", *name)
                }
                instructions.push(Split(patterns.len()));
                let mut size = 0;
                for (i, p) in patterns.iter().enumerate() {
                    let stack_size = stack_index + patterns.len();
                    size += self.compile_pattern(p, branches, instructions, stack_size, patterns.len() - i - 1);
                }
                size + patterns.len()
            }
            &NumberPattern(number) => {
                self.newStackVar(Name { name: pattern_index.to_str(), uid: 0 });
                instructions.push(Push(stack_index - pattern_index));
                instructions.push(Eval);
                instructions.push(PushInt(number));
                instructions.push(IntEQ);
                instructions.push(JumpFalse(0));
                0
            }
            &IdentifierPattern(ref ident) => {
                self.newStackVar(ident.name.clone());
                0
            }
        }
    }
}

///Attempts to find the actual type of the for the variable which has a constraint
fn try_find_instance_type<'a>(class_var: &TypeVariable, class_type: &Type, actual_type: &'a Type) -> Option<&'a str> {
    match (class_type, actual_type) {
        (&TypeVariable(ref var), _) if var == class_var => {
            //Found the class variable so return the name of the type
            match extract_applied_type(actual_type) {
                &TypeOperator(ref op) => { Some(op.name.as_slice()) }
                _ => None
            }
        }
        (&TypeOperator(ref class_op), &TypeOperator(ref actual_op)) => {
            assert_eq!(class_op.name, actual_op.name);
            None
        }
        (&TypeApplication(ref lhs1, ref rhs1), &TypeApplication(ref lhs2, ref rhs2)) => {
            try_find_instance_type(class_var, *lhs1, *lhs2)
                .or_else(|| try_find_instance_type(class_var, *rhs1, *rhs2))
        }
        _ => None
    }
}

#[allow(dead_code)]
pub fn compile(contents: &str) -> Assembly {
    let mut type_env = TypeEnvironment::new();
    compile_with_type_env(&mut type_env, [], contents)
}
#[allow(dead_code)]
pub fn compile_with_type_env(type_env: &mut TypeEnvironment, assemblies: &[&Assembly], contents: &str) -> Assembly {
    use parser::Parser;

    let mut parser = Parser::new(contents.chars()); 
    let mut module = parser.module();
    for assem in assemblies.iter() {
        type_env.add_types(*assem);
    }
    type_env.typecheck_module(&mut module);
    let core_module = do_lambda_lift(translate_module(module));
    let mut compiler = Compiler::new(type_env);
    for assem in assemblies.iter() {
        compiler.assemblies.push(*assem);
    }
    compiler.compileModule(&core_module)
}


#[cfg(test)]
mod tests {

use compiler::*;
use typecheck::TypeEnvironment;
use std::io::File;

#[test]
fn add() {
    let file = "main = primIntAdd 1 2";
    let assembly = compile(file);

    assert_eq!(assembly.superCombinators[0].instructions, ~[PushInt(2), PushInt(1), Add, Update(0), Unwind]);
}

#[test]
fn add_double() {
    let file =
r"add x y = primDoubleAdd x y
main = add 2. 3.";
    let assembly = compile(file);

    assert_eq!(assembly.superCombinators[0].instructions, ~[Push(1), Eval, Push(0), Eval, DoubleAdd, Update(0), Pop(2), Unwind]);
    assert_eq!(assembly.superCombinators[1].instructions, ~[PushFloat(3.), PushFloat(2.), PushGlobal(0), Mkap, Mkap, Eval, Update(0), Unwind]);
}
#[test]
fn push_num_double() {
    let file =
r"main = primDoubleAdd 2 3";
    let assembly = compile(file);

    assert_eq!(assembly.superCombinators[0].instructions, ~[PushFloat(3.), PushFloat(2.), DoubleAdd, Update(0), Unwind]);
}

#[test]
fn application() {
    let file =
r"add x y = primIntAdd x y
main = add 2 3";
    let assembly = compile(file);

    assert_eq!(assembly.superCombinators[1].instructions, ~[PushInt(3), PushInt(2), PushGlobal(0), Mkap, Mkap, Eval, Update(0), Unwind]);
}

#[test]
fn compile_constructor() {
    let file =
r"main = primIntAdd 1 0 : []";
    let assembly = compile(file);

    assert_eq!(assembly.superCombinators[0].instructions, ~[Pack(0, 0), PushInt(0), PushInt(1), Add, Pack(1, 2), Update(0), Unwind]);
}

#[test]
fn compile_tuple() {
    let file =
r"test x y = (primIntAdd 0 1, x, y)";
    let assembly = compile(file);

    assert_eq!(assembly.superCombinators[0].instructions, ~[Push(1), Push(0), PushInt(1), PushInt(0), Add, Pack(0, 3), Update(0), Pop(2), Unwind]);
}

#[test]
fn compile_case() {
    let file =
r"main = case [primIntAdd 1 0] of
    : x xs -> x
    [] -> 2";
    let assembly = compile(file);


    assert_eq!(assembly.superCombinators[0].instructions, ~[Pack(0, 0), PushInt(0), PushInt(1), Add, Pack(1, 2),
        Push(0), CaseJump(1), Jump(14), Split(2), Push(1), Eval, Slide(2), Jump(22), Pop(2),
        Push(0), CaseJump(0), Jump(22), Split(0), PushInt(2), Slide(0), Jump(22), Pop(0), Slide(1), Eval, Update(0), Unwind]);
}

#[test]
fn compile_nested_case() {
    let file =
r"main = case [primIntAdd 1 0] of
    : 1 xs -> primIntAdd 1 1
    [] -> 2";
    let assembly = compile(file);

    assert_eq!(assembly.superCombinators[0].instructions, ~[Pack(0, 0), PushInt(0), PushInt(1), Add, Pack(1, 2),
        Push(0), CaseJump(1), Jump(20), Split(2), Push(1), Eval, PushInt(1), IntEQ, JumpFalse(19), PushInt(1), PushInt(1), Add, Slide(2), Jump(28), Pop(2),
        Push(0), CaseJump(0), Jump(28), Split(0), PushInt(2), Slide(0), Jump(28), Pop(0), Slide(1), Eval, Update(0), Unwind]);
}

#[test]
fn compile_class_constraints() {
    let file =
r"class Test a where
    test :: a -> Int

instance Test Int where
    test x = x

main = test (primIntAdd 6 0)";
    let assembly = compile(file);

    let main = &assembly.superCombinators[1];
    assert_eq!(main.name.name, ~"main");
    assert_eq!(main.instructions, ~[PushInt(0), PushInt(6), Add, PushGlobal(0), Mkap, Eval, Update(0), Unwind]);
}

#[test]
fn compile_class_constraints_unknown() {
    let file =
r"class Test a where
    test :: a -> Int

instance Test Int where
    test x = x

main x = primIntAdd (test x) 6";
    let assembly = compile(file);

    let main = assembly.superCombinators[1];
    assert_eq!(main.name.name, ~"main");
    assert_eq!(main.instructions, ~[PushInt(6), Push(1), PushDictionaryMember(0), Mkap, Eval, Add, Update(0), Pop(2), Unwind]);
}

#[test]
fn compile_prelude() {
    let mut type_env = TypeEnvironment::new();
    let prelude = compile_with_type_env(&mut type_env, [], File::open(&Path::new("Prelude.hs")).read_to_str().unwrap());

    let assembly = compile_with_type_env(&mut type_env, [&prelude], r"main = id (primIntAdd 2 0)");

    let sc = &assembly.superCombinators[0];
    let id_index = prelude.superCombinators.iter().position(|sc| sc.name.equiv(& &"id")).unwrap();
    assert_eq!(sc.instructions, ~[PushInt(0), PushInt(2), Add, PushGlobal(id_index), Mkap, Eval, Update(0), Unwind]);
}

}
