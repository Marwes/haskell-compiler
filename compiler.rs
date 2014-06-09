use interner::*;
use core::*;
use module::{int_type, double_type, function_type, Qualified};
use typecheck::{Types, DataTypes, TypeEnvironment};
use scoped_map::ScopedMap;
use std::iter::range_step;
use std::default::Default;
use std::vec::FromVec;
use std::io::IoResult;

use core::translate::{translate_module};
use lambda_lift::do_lambda_lift;
use renamer::rename_module;
use primitive::primitives;

#[deriving(PartialEq, Clone, Show)]
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
    PushPrimitive(uint)
}
#[deriving(Show)]
enum Var<'a> {
    StackVariable(uint),
    GlobalVariable(uint),
    ConstructorVariable(u16, u16),
    ClassVariable(&'a Type, &'a TypeVariable),
    ConstraintVariable(uint, &'a Type, &'a[Constraint]),
    PrimitiveVariable(uint)
}

impl <'a> Clone for Var<'a> {
    fn clone(&self) -> Var<'a> {
        match self {
            &StackVariable(x) => StackVariable(x),
            &GlobalVariable(x) => GlobalVariable(x),
            &ConstructorVariable(x, y) => ConstructorVariable(x, y),
            &ClassVariable(x, y) => ClassVariable(x, y),
            &ConstraintVariable(x, y, z) => ConstraintVariable(x, y, z),
            &PrimitiveVariable(x) => PrimitiveVariable(x)
        }
    }
}

pub struct SuperCombinator {
    pub arity : uint,
    pub name: Name,
    pub assembly_id: uint,
    pub instructions : ~[Instruction],
    pub typ: Qualified<Type>
}
impl SuperCombinator {
    fn new() -> SuperCombinator {
        SuperCombinator { arity : 0, name: Name { name: intern(""), uid: 0}, instructions : ~[], typ: Default::default(), assembly_id: 0 }
    }
}

pub struct Assembly {
    pub superCombinators: ~[SuperCombinator],
    pub instance_dictionaries: ~[~[uint]],
    pub classes: ~[Class],
    pub instances: ~[(~[Constraint], Type)],
    pub data_definitions: ~[DataDefinition<Name>],
    pub offset: uint
}

trait Globals {
    ///Lookup a global variable
    fn find_global<'a>(&'a self, name: &Name) -> Option<Var<'a>>;
    fn find_constructor(&self, name: InternedStr) -> Option<(u16, u16)>;
}

impl Globals for Assembly {
    fn find_global<'a>(&'a self, name: &Name) -> Option<Var<'a>> {
        let mut index = 0;
        for sc in self.superCombinators.iter() {
            if *name == sc.name {
                if sc.typ.constraints.len() > 0 {
                    return Some(ConstraintVariable(self.offset + index, &sc.typ.value, sc.typ.constraints));
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
                    return Some(ClassVariable(&decl.typ.value, &class.variable));
                }
            }
        }
        
        self.find_constructor(name.name).map(|(tag, arity)| ConstructorVariable(tag, arity))
    }
    fn find_constructor(&self, name: InternedStr) -> Option<(u16, u16)> {
        for data_def in self.data_definitions.iter() {
            for ctor in data_def.constructors.iter() {
                if name == ctor.name.name {
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
                return Some(ClassVariable(&decl.typ.value, &class.variable));
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

fn find_constructor(module: &Module<Id>, name: InternedStr) -> Option<(u16, u16)> {

    for dataDef in module.data_definitions.iter() {
        for ctor in dataDef.constructors.iter() {
            if name == ctor.name.name {
                return Some((ctor.tag as u16, ctor.arity as u16));
            }
        }
    }
    None
}

impl Types for Module<Id> {
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Type> {
        for bind in self.bindings.iter() {
            if bind.name.name == *name {
                return Some(bind.expression.get_type());
            }
        }

        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                if name.name == decl.name {
                    return Some(&decl.typ.value);
                }
            }
        }
        for data in self.data_definitions.iter() {
            for ctor in data.constructors.iter() {
                if *name == ctor.name {
                    return Some(&ctor.typ.value);
                }
            }
        }
        return None;
    }

    fn find_class<'a>(&'a self, name: InternedStr) -> Option<&'a Class> {
        self.classes.iter().find(|class| name == class.name)
    }

    fn find_instance<'a>(&'a self, classname: InternedStr, typ: &Type) -> Option<(&'a [Constraint], &'a Type)> {
        for &(ref constraints, ref op) in self.instances.iter() {
            match op {
                &TypeApplication(ref op, ref t) => {
                    let x = match extract_applied_type(*op) {
                        &TypeOperator(ref x) => x,
                        _ => fail!()
                    };
                    let y = match extract_applied_type(*t) {
                        &TypeOperator(ref x) => x,
                        _ => fail!()
                    };
                    let z = match extract_applied_type(typ) {
                        &TypeOperator(ref x) => x,
                        _ => fail!()
                    };
                    if classname == x.name && y.name == z.name {
                        let c : &[Constraint] = *constraints;
                        let o : &Type = *t;
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
                func(decl.typ.constraints);
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
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Type> {
        for sc in self.superCombinators.iter() {
            if sc.name == *name {
                return Some(&sc.typ.value);
            }
        }
        
        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                if name.name == decl.name {
                    return Some(&decl.typ.value);
                }
            }
        }

        for data_def in self.data_definitions.iter() {
            for ctor in data_def.constructors.iter() {
                if *name == ctor.name {
                    return Some(&ctor.typ.value);
                }
            }
        }
        return None;
    }

    fn find_class<'a>(&'a self, name: InternedStr) -> Option<&'a Class> {
        self.classes.iter().find(|class| name == class.name)
    }
    fn find_instance<'a>(&'a self, classname: InternedStr, typ: &Type) -> Option<(&'a [Constraint], &'a Type)> {
        for &(ref constraints, ref op) in self.instances.iter() {
            match op {
                &TypeApplication(ref op, ref t) => {
                    let x = match extract_applied_type(*op) {
                        &TypeOperator(ref x) => x,
                        _ => fail!()
                    };
                    let y = match extract_applied_type(*t) {
                        &TypeOperator(ref x) => x,
                        _ => fail!()
                    };
                    let z = match extract_applied_type(typ) {
                        &TypeOperator(ref x) => x,
                        _ => fail!()
                    };
                    if classname == x.name && y.name == z.name {
                        let c : &[Constraint] = *constraints;
                        let o : &Type = *t;
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
            func(sc.typ.constraints);
        }
        
        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                func(decl.typ.constraints);
            }
        }
    }
}

impl DataTypes for Assembly {
    fn find_data_type<'a>(&'a self, name: InternedStr) -> Option<&'a DataDefinition<Name>> {
        for data in self.data_definitions.iter() {
            if name == extract_applied_type(&data.typ.value).op().name {
                return Some(data);
            }
        }
        None
    }
}

impl Instruction {
    fn stack_change(&self) -> int {
        match *self {
            Add | Sub | Multiply | Divide | Remainder | IntEQ | IntLT | IntLE | IntGT | IntGE | 
            DoubleAdd |  DoubleSub |  DoubleMultiply |  DoubleDivide |  DoubleRemainder |  DoubleEQ |
            DoubleLT |  DoubleLE |  DoubleGT |  DoubleGE => -1,
            IntToDouble |  DoubleToInt => 0,
            Push(..) | PushGlobal(..) | PushInt(..) | PushFloat(..) | PushChar(..) => 1,
            Mkap => -1,
            Eval | Unwind | Update(..) => 0,
            Pop(s) => -(s as int),
            Slide(s) => -(s as int),
            Split(s) => (s as int) - 1, 
            Pack(_, s) => 1 - (s as int),
            CaseJump(..) | Jump(..) | JumpFalse(..) => 0,
            PushDictionary(..) | PushDictionaryMember(..) | PushPrimitive(..) => 1
        }
    }
}

pub struct Compiler<'a> {
    pub type_env: &'a TypeEnvironment<'a>,
    ///Hashmap containging class names mapped to the functions it contains
    pub instance_dictionaries: Vec<(~[(InternedStr, Type)], ~[uint])>,
    pub stackSize : uint,
    ///Array of all the assemblies which can be used to lookup functions in
    pub assemblies: Vec<&'a Assembly>,
    module: Option<&'a Module<Id>>,
    variables: ScopedMap<Name, Var<'a>>
}


impl <'a> Compiler<'a> {
    pub fn new(type_env: &'a TypeEnvironment) -> Compiler<'a> {
        let mut variables = ScopedMap::new();
        for (i, &(name, _)) in primitives().iter().enumerate() {
            variables.insert(Name { name: intern(name), uid: 0}, PrimitiveVariable(i));
        }
        Compiler { type_env: type_env, instance_dictionaries: Vec::new(),
            stackSize : 0, assemblies: Vec::new(),
            module: None,
            variables: variables
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
            sc.name = bind.name.name.clone();
            superCombinators.push(sc);
        }

        for &(_, ref dict) in self.instance_dictionaries.iter() {
            instance_dictionaries.push(dict.clone());
        }
        self.module = None;
        Assembly {
            superCombinators: FromVec::from_vec(superCombinators),
            instance_dictionaries: FromVec::from_vec(instance_dictionaries),
            offset: self.assemblies.iter().flat_map(|assembly| assembly.superCombinators.iter()).len(),
            classes: module.classes.clone(),
            instances: FromVec::<(~[Constraint], Type)>::from_vec(module.instances.iter().map(|x| x.clone()).collect()),
            data_definitions: FromVec::from_vec(data_definitions)
        }
    }

    fn compileBinding(&mut self, bind : &Binding<Id>) -> SuperCombinator {
        let mut comb = SuperCombinator::new();
        comb.assembly_id = self.assemblies.len();
        comb.typ = Qualified {
            constraints: bind.name.constraints.clone(),
            value: bind.name.typ.clone(),
        };
        debug!("Compiling binding {} :: {}", comb.name, comb.typ);
        let dict_arg = if bind.name.constraints.len() > 0 { 1 } else { 0 };
        let mut instructions = Vec::new();
        self.scope(|this| {
            if dict_arg == 1 {
                this.newStackVar(Name { name: intern("$dict"), uid: 0 });
            }
            debug!("{} {}\n {}", bind.name, dict_arg, bind.expression);
            let arity = this.compile_lambda_binding(&bind.expression, &mut instructions);
            comb.arity = arity + dict_arg;
            instructions.push(Update(0));
            if comb.arity != 0 {
                instructions.push(Pop(comb.arity));
            }
            instructions.push(Unwind);
        });
        comb.instructions = FromVec::from_vec(instructions);
        debug!("{} :: {} compiled as:\n{}", comb.name, comb.typ, comb.instructions);
        comb
    }

    fn compile_lambda_binding(&mut self, expr: &Expr<Id>, instructions: &mut Vec<Instruction>) -> uint {
        match expr {
            &Lambda(ref ident, ref body) => {
                self.newStackVar(ident.name.clone());
                1 + self.compile_lambda_binding(*body, instructions)
            }
            _ => {
                self.compile(expr, instructions, true);
                0
            }
        }
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
                "[]" => Some(ConstructorVariable(0, 0)),
                ":" => Some(ConstructorVariable(1, 2)),
                _ => None
            }
        })
    }

    fn find_constructor(&self, identifier : InternedStr) -> Option<(u16, u16)> {
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
            let identifier = identifier.as_slice();
            if identifier.len() >= 3 && identifier.char_at(0) == '('
            && identifier.char_at(identifier.len() - 1) == ')'
            && identifier.chars().skip(1).take(identifier.len() - 2).all(|c| c == ',') {
                return Some((0, (identifier.len() - 1) as u16));
            }
            match identifier {
                "[]" => Some((0, 0)),
                ":" => Some((1, 2)),
                _ => None
            }
        })
    }

    fn find_class<'r>(&'r self, name: InternedStr) -> Option<&'r Class> {
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
    fn new_var_at(&mut self, identifier : Name, index: uint) {
        self.variables.insert(identifier, StackVariable(index));
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
                        debug!("{}", var);
                        match var {
                            StackVariable(index) => { instructions.push(Push(index)); None }
                            GlobalVariable(index) => { instructions.push(PushGlobal(index)); None }
                            ConstructorVariable(tag, arity) => { instructions.push(Pack(tag, arity)); None }
                            PrimitiveVariable(index) => { instructions.push(PushPrimitive(index)); None }
                            ClassVariable(typ, var) => self.compile_instance_variable(expr.get_type(), instructions, &name.name, typ, var),
                            ConstraintVariable(index, bind_type, constraints) => {
                                debug!("{} {} {}", name.as_slice(), bind_type, constraints);
                                let x = self.compile_with_constraints(&name.name, expr.get_type(), bind_type, constraints, instructions);
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
                        if literal.typ == int_type() {
                            instructions.push(PushInt(i));
                        }
                        else if literal.typ == double_type() {
                            instructions.push(PushFloat(i as f64));
                        }
                        else {
                            let fromInteger = Identifier(Id {
                                name: Name { name: intern("fromInteger"), uid: 999999 }, 
                                typ: function_type_(int_type(), literal.typ.clone()),
                                constraints: ~[]
                            });
                            let number = Literal(Literal { typ: int_type(), value: Integral(i) });
                            let apply = Apply(box fromInteger, box number);
                            self.compile(&apply, instructions, strict);
                        }
                    }
                    &Fractional(f) => {
                        if literal.typ == double_type() {
                            instructions.push(PushFloat(f));
                        }
                        else {
                            let fromRational = Identifier(Id {
                                name: Name { name: intern("fromRational"), uid: 999999 }, 
                                typ: function_type_(double_type(), literal.typ.clone()),
                                constraints: ~[]
                            });
                            let number = Literal(Literal {
                                typ: double_type(),
                                value: Fractional(f)
                            });
                            let apply = Apply(box fromRational, box number);
                            self.compile(&apply, instructions, strict);
                        }
                    }
                    &String(ref s) => {
                        instructions.push(Pack(0, 0));
                        for c in s.as_slice().chars().rev() {
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
                    //The stack has increased by 1 until the function compiles add reduces it wtih Pack or Mkap
                    self.stackSize += 1;
                    self.compile(*func, instructions, false);
                    self.stackSize -= 1;
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
            &Let(ref bindings, ref body) => {
                self.scope(|this| {
                    for bind in bindings.iter() {
                        this.newStackVar(bind.name.name.clone());
                        //Workaround since this compiles non-recursive bindings
                        //The stack is not actually increased until after the binding is compiled
                        this.stackSize -= 1;
                        this.compile(&bind.expression, instructions, false);
                        this.stackSize += 1;
                    }
                    this.compile(*body, instructions, strict);
                    instructions.push(Slide(bindings.len()));
                });
            }
            &Case(ref body, ref alternatives) => {
                self.compile(*body, instructions, true);
                self.stackSize += 1;
                //Dummy variable for the case expression
                //Storage for all the jumps that should go to the end of the case expression
                let mut end_branches = Vec::new();
                for i in range(0, alternatives.len()) {
                    let alt = &alternatives[i];

                    self.scope(|this| {
                        let pattern_start = instructions.len() as int;
                        let mut branches = Vec::new();
                        let stack_increase = this.compile_pattern(&alt.pattern, &mut branches, instructions, this.stackSize - 1);
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
                for branch in end_branches.iter() {
                    *instructions.get_mut(*branch) = Jump(instructions.len());
                }
                //Remove the matched expr
                instructions.push(Slide(1));
                if strict {
                    instructions.push(Eval);
                }
            }
            &Lambda(_, _) => fail!("Error: Found non-lifted lambda when compiling expression")
        }
    }

    ///Compile a function which is defined in a class
    fn compile_instance_variable(&self, actual_type: &Type, instructions: &mut Vec<Instruction>, name: &Name, typ: &Type, var: &TypeVariable) -> Option<(~[(InternedStr, Type)], ~[uint])> {
        match try_find_instance_type(var, typ, actual_type) {
            Some(typename) => {
                //We should be able to retrieve the instance directly
                let mut b = String::from_str("#");
                b.push_str(typename);
                b.push_str(name.as_slice());
                let instance_fn_name = Name { name: intern(b.as_slice()), uid: 0 };
                match self.find(&instance_fn_name) {
                    Some(GlobalVariable(index)) => {
                        instructions.push(PushGlobal(index));
                        None
                    }
                    Some(ConstraintVariable(index, function_type, constraints)) => {
                        debug!("xxx {} {} {} {}", instance_fn_name.as_slice(), actual_type, function_type, constraints);
                        let dict = self.compile_with_constraints(&instance_fn_name, actual_type, function_type, constraints, instructions);
                        instructions.push(PushGlobal(index));
                        instructions.push(Mkap);
                        dict
                    }
                    _ => fail!("Unregistered instance function {}", name)
                }
            }
            None => {
                let constraints = self.type_env.find_constraints(actual_type);
                debug!("aaa {} {} {}\n {}", var, typ, actual_type, constraints);
                self.compile_with_constraints(name, actual_type, typ, constraints, instructions)
            }
        }
    }

    ///Compile the loading of a variable which has constraints and will thus need to load a dictionary with functions as well
    fn compile_with_constraints(&self, name: &Name, actual_type: &Type, function_type: &Type, constraints: &[Constraint], instructions: &mut Vec<Instruction>) -> Option<(~[(InternedStr, Type)], ~[uint])> {
        match self.find(&Name { name: intern("$dict"), uid: 0}) {
            Some(StackVariable(_)) => {
                //Push dictionary or member of dictionary
                match self.push_dictionary_member(constraints, name.name) {
                    Some(index) => instructions.push(PushDictionaryMember(index)),
                    None => instructions.push(Push(0))
                }
                None
            }
            _ => {
                //get dictionary index
                //push dictionary
                let dictionary_key = self.type_env.find_specialized_instances(function_type, actual_type);
                let (index, dict) = self.find_dictionary_index(dictionary_key);
                instructions.push(PushDictionary(index));
                dict
            }
        }
    }

    ///Lookup which index in the instance dictionary that holds the function called 'name'
    fn push_dictionary_member(&self, constraints: &[Constraint], name: InternedStr) -> Option<uint> {
        if constraints.len() == 0 {
            fail!("Attempted to push dictionary member '{}' with no constraints", name)
        }
        for c in constraints.iter() {
            match self.find_class(c.class) {
                Some(class) => {
                    for ii in range(0, class.declarations.len()) {
                        if class.declarations[ii].name == name {
                            return Some(ii)
                        }
                    }
                }
                None => fail!("Undefined instance {}", c)
            }
        }
        None
    }

    ///Find the index of the instance dictionary for the constraints and types in 'constraints'
    ///Returns the index and possibly a new dictionary which needs to be added to the assemblies dictionaries
    fn find_dictionary_index(&self, constraints: &[(InternedStr, Type)]) -> (uint, Option<(~[(InternedStr, Type)], ~[uint])>) {


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
                        let x = match extract_applied_type(typ) {
                            &TypeOperator(ref x) => x,
                            _ => fail!("{}", typ)
                        };
                        let mut b = String::from_str("#");
                        b.push_str(x.name.as_slice());
                        b.push_str(decl.name.as_slice());
                        let f = intern(b.as_slice());
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
        (dict_len, Some((constraints.to_owned(), FromVec::from_vec(function_indexes))))
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
                                self.stackSize += 1;
                                self.compile(*arg2, instructions, true);
                                self.stackSize -= 1;
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
                let n: &str = name.name.name.as_slice();
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

    fn compile_pattern(&mut self, pattern: &Pattern<Id>, branches: &mut Vec<uint>, instructions: &mut Vec<Instruction>, stack_size: uint) -> uint {
        debug!("Pattern {} at {}", pattern, stack_size);
        match pattern {
            &ConstructorPattern(ref name, ref patterns) => {
                instructions.push(Push(stack_size));
                match self.find_constructor(name.name.name) {
                    Some((tag, _)) => {
                        instructions.push(CaseJump(tag as uint));
                        branches.push(instructions.len());
                        instructions.push(Jump(0));
                    }
                    _ => fail!("Undefined constructor {}", *name)
                }
                instructions.push(Split(patterns.len()));
                self.stackSize += patterns.len();
                for (i, p) in patterns.iter().enumerate() {
                    self.new_var_at(p.name.clone(), self.stackSize - patterns.len() + i);
                }
                patterns.len()
            }
            &NumberPattern(number) => {
                self.new_var_at(Name { name: intern(stack_size.to_str().as_slice()), uid: 0 }, stack_size);
                instructions.push(Push(stack_size));
                instructions.push(Eval);
                instructions.push(PushInt(number));
                instructions.push(IntEQ);
                instructions.push(JumpFalse(0));
                0
            }
            &IdentifierPattern(ref ident) => {
                self.new_var_at(ident.name.clone(), stack_size);
                0
            }
            &WildCardPattern => {
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

    let mut parser = Parser::new(contents.as_slice().chars()); 
    let mut module = rename_module(parser.module());
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

pub fn compile_module(module: &str) -> IoResult<Vec<Assembly>> {
    use typecheck::typecheck_module;
    use compiler::Compiler;
    let (modules, mut type_env) = try!(typecheck_module(module));
    let core_modules: Vec<Module<Id<Name>>> = modules.move_iter()
        .map(|module| do_lambda_lift(translate_module(module)))
        .collect();
    let mut assemblies = Vec::new();
    for module in core_modules.iter() {
        let x = {
            let mut compiler = Compiler::new(&mut type_env);
            for a in assemblies.iter() {
                compiler.assemblies.push(a);
            }
            compiler.compileModule(module)
        };
        assemblies.push(x);
    }
    Ok(assemblies)
}

#[cfg(test)]
mod tests {

use interner::*;
use compiler::*;
use typecheck::TypeEnvironment;
use std::io::File;
use test::Bencher;

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
    x:xs -> x
    [] -> 2";
    let assembly = compile(file);


    assert_eq!(assembly.superCombinators[0].instructions, ~[Pack(0, 0), PushInt(0), PushInt(1), Add, Pack(1, 2),
        Push(0), CaseJump(1), Jump(14), Split(2), Push(1), Eval, Slide(2), Jump(22), Pop(2),
        Push(0), CaseJump(0), Jump(22), Split(0), PushInt(2), Slide(0), Jump(22), Pop(0), Slide(1), Eval, Update(0), Unwind]);
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
    assert_eq!(main.name.name, intern("main"));
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
    assert_eq!(main.name.name, intern("main"));
    assert_eq!(main.instructions, ~[PushInt(6), Push(1), PushDictionaryMember(0), Mkap, Eval, Add, Update(0), Pop(2), Unwind]);
}

#[test]
fn compile_prelude() {
    let mut type_env = TypeEnvironment::new();
    let prelude = compile_with_type_env(&mut type_env, [], File::open(&Path::new("Prelude.hs")).read_to_str().unwrap().as_slice());

    let assembly = compile_with_type_env(&mut type_env, [&prelude], r"main = id (primIntAdd 2 0)");

    let sc = &assembly.superCombinators[0];
    let id_index = prelude.superCombinators.iter().position(|sc| sc.name.name == intern("id")).unwrap();
    assert_eq!(sc.instructions, ~[PushInt(0), PushInt(2), Add, PushGlobal(id_index), Mkap, Eval, Update(0), Unwind]);
}

#[test]
fn generics_do_not_propagate() {
    //Test that the type of 'i' does not get overwritten by the use inside the let binding
    //after typechecking the let binding, retrieving the type for 'i' the second time should
    //not make the typechecker instantiate a new variable but keep using the original one
    //This is something the typechecker should notice but for now the compiler will have to do it
    compile(
r"
class Num a where
    fromInteger :: Int -> a
instance Num Int where
    fromInteger x = x
class Integral a where
    rem :: a -> a -> a

instance Integral Int where
    rem x y = primIntRemainder x y

showInt :: Int -> [Char]
showInt i =
    let
        i2 = i `rem` 10
    in showInt (i `rem` 7)
");
}

#[test]
fn binding_pattern() {
    compile(r"
test f (x:xs) = f x : test f xs
test _ [] = []
");
}

#[bench]
fn bench_prelude(b: &mut Bencher) {
    use lambda_lift::do_lambda_lift;
    use core::translate::translate_module;
    use renamer::rename_module;
    use parser::Parser;

    let path = &Path::new("Prelude.hs");
    let contents = File::open(path).read_to_str().unwrap();
    let mut parser = Parser::new(contents.as_slice().chars());
    let mut module = rename_module(parser.module());
    let mut type_env = TypeEnvironment::new();
    type_env.typecheck_module(&mut module);
    let core_module = do_lambda_lift(translate_module(module));
    b.iter(|| {
        let mut compiler = Compiler::new(&type_env);
        compiler.compileModule(&core_module)
    });
}
}
