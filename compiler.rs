use interner::*;
use core::*;
use core::Expr::*;
use types::{int_type, double_type, function_type, function_type_, qualified};
use typecheck::{Types, DataTypes, TypeEnvironment, find_specialized_instances};
use scoped_map::ScopedMap;
use std::iter::range_step;
use std::io::IoResult;

use core::translate::{translate_module, translate_modules};
use lambda_lift::do_lambda_lift;
use renamer::rename_module;
use builtins::builtins;

use self::Instruction::*;

#[derive(PartialEq, Clone, Show)]
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
    PushBuiltin(uint),
    MkapDictionary,
    ConstructDictionary(uint),
    PushDictionaryRange(uint, uint)
}
#[derive(Show)]
enum Var<'a> {
    Stack(uint),
    Global(uint),
    Constructor(u16, u16),
    Class(&'a Type, &'a [Constraint<Name>], &'a TypeVariable),
    Constraint(uint, &'a Type, &'a[Constraint<Name>]),
    Builtin(uint),
    Primitive(uint, Instruction),
    Newtype
}

static unary_primitives: &'static [(&'static str, Instruction)] = &[
    ("primIntToDouble", IntToDouble),
    ("primDoubleToInt", DoubleToInt),
];

static binary_primitives: &'static [(&'static str, Instruction)] = &[
    ("primIntAdd", Add),
    ("primIntSubtract", Sub),
    ("primIntMultiply", Multiply),
    ("primIntDivide", Divide),
    ("primIntRemainder", Remainder),
    ("primIntEQ", IntEQ),
    ("primIntLT", IntLT),
    ("primIntLE", IntLE),
    ("primIntGT", IntGT),
    ("primIntGE", IntGE),
    ("primDoubleAdd", DoubleAdd),
    ("primDoubleSubtract", DoubleSub),
    ("primDoubleMultiply", DoubleMultiply),
    ("primDoubleDivide", DoubleDivide),
    ("primDoubleRemainder", DoubleRemainder),
    ("primDoubleEQ", DoubleEQ),
    ("primDoubleLT", DoubleLT),
    ("primDoubleLE", DoubleLE),
    ("primDoubleGT", DoubleGT),
    ("primDoubleGE", DoubleGE),
];


impl <'a> Clone for Var<'a> {
    fn clone(&self) -> Var<'a> {
        match *self {
            Var::Stack(x) => Var::Stack(x),
            Var::Global(x) => Var::Global(x),
            Var::Constructor(x, y) => Var::Constructor(x, y),
            Var::Class(x, y, z) => Var::Class(x, y, z),
            Var::Constraint(x, y, z) => Var::Constraint(x, y, z),
            Var::Builtin(x) => Var::Builtin(x),
            Var::Primitive(x, y) => Var::Primitive(x, y),
            Var::Newtype => Var::Newtype
        }
    }
}

pub struct SuperCombinator {
    pub arity : uint,
    pub name: Name,
    pub assembly_id: uint,
    pub instructions : Vec<Instruction>,
    pub typ: Qualified<Type, Name>
}
pub struct Assembly {
    pub superCombinators: Vec<SuperCombinator>,
    pub instance_dictionaries: Vec<Vec<uint>>,
    pub classes: Vec<Class<Id>>,
    pub instances: Vec<(Vec<Constraint<Name>>, Type)>,
    pub data_definitions: Vec<DataDefinition<Name>>,
    pub offset: uint
}

trait Globals {
    ///Lookup a global variable
    fn find_global<'a>(&'a self, name: Name) -> Option<Var<'a>>;
    fn find_constructor(&self, name: Name) -> Option<(u16, u16)>;
}

impl Globals for Assembly {
    fn find_global<'a>(&'a self, name: Name) -> Option<Var<'a>> {
        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                if decl.name == name {
                    return Some(Var::Class(&decl.typ.value, decl.typ.constraints, &class.variable));
                }
            }
        }
        
        let mut index = 0;
        for sc in self.superCombinators.iter() {
            if name == sc.name {
                if sc.typ.constraints.len() > 0 {
                    return Some(Var::Constraint(self.offset + index, &sc.typ.value, sc.typ.constraints));
                }
                else {
                    return Some(Var::Global(self.offset + index));
                }
            }
            index += 1;
        }
        self.find_constructor(name).map(|(tag, arity)| Var::Constructor(tag, arity))
    }
    fn find_constructor(&self, name: Name) -> Option<(u16, u16)> {
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

fn find_global<'a>(module: &'a Module<Id>, offset: uint, name: Name) -> Option<Var<'a>> {
    
    for class in module.classes.iter() {
        for decl in class.declarations.iter() {
            if decl.name == name {
                return Some(Var::Class(&decl.typ.value, decl.typ.constraints, &class.variable));
            }
        }
    }

    let mut global_index = 0;
    module.bindings.iter()
        .chain(module.instances.iter().flat_map(|instance| instance.bindings.iter()))
        .chain(module.classes.iter().flat_map(|c| c.bindings.iter()))
        .find(|bind| { global_index += 1; bind.name.name == name })
        .map(|bind| {
            global_index -= 1;
            let typ = bind.expression.get_type();
            let constraints = &bind.name.typ.constraints;
            if constraints.len() > 0 {
                Var::Constraint(offset + global_index, typ, *constraints)
            }
            else {
                Var::Global(offset + global_index)
            }
        })
        .or_else(|| {
            module.newtypes.iter()
                .find(|newtype| newtype.constructor_name == name)
                .map(|_| Var::Newtype)
        })
        .or_else(|| {
            find_constructor(module, name)
                .map(|(tag, arity)| Var::Constructor(tag, arity))
        })
}

fn find_constructor(module: &Module<Id>, name: Name) -> Option<(u16, u16)> {

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
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Qualified<Type, Name>> {
        for bind in self.bindings.iter() {
            if bind.name.name == *name {
                return Some(&bind.name.typ);
            }
        }

        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                if *name == decl.name {
                    return Some(&decl.typ);
                }
            }
        }
        for data in self.data_definitions.iter() {
            for ctor in data.constructors.iter() {
                if *name == ctor.name {
                    return Some(&ctor.typ);
                }
            }
        }
        self.newtypes.iter()
            .find(|newtype| newtype.constructor_name == *name)
            .map(|newtype| &newtype.constructor_type)
    }

    fn find_class<'a>(&'a self, name: Name) -> Option<(&'a [Constraint<Name>], &'a TypeVariable, &'a [TypeDeclaration<Name>])> {
        self.classes.iter()
            .find(|class| name == class.name)
            .map(|class| (class.constraints.as_slice(), &class.variable, class.declarations.as_slice()))
    }

    fn find_instance<'a>(&'a self, classname: Name, typ: &Type) -> Option<(&'a [Constraint<Name>], &'a Type)> {
        for instance in self.instances.iter() {
            let y = match extract_applied_type(&instance.typ) {
                &Type::Constructor(ref x) => x,
                _ => panic!()
            };
            let z = match extract_applied_type(typ) {
                &Type::Constructor(ref x) => x,
                _ => panic!()
            };
            if classname == instance.classname && y.name == z.name {
                return Some((instance.constraints.as_slice(), &instance.typ));
            }
        }
        None
    }
}

fn extract_applied_type<'a>(typ: &'a Type) -> &'a Type {
    match typ {
        &Type::Application(ref lhs, _) => extract_applied_type(*lhs),
        _ => typ
    }
}

impl Types for Assembly {
    ///Lookup a type
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Qualified<Type, Name>> {
        for sc in self.superCombinators.iter() {
            if sc.name == *name {
                return Some(&sc.typ);
            }
        }
        
        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                if *name == decl.name {
                    return Some(&decl.typ);
                }
            }
        }

        for data_def in self.data_definitions.iter() {
            for ctor in data_def.constructors.iter() {
                if *name == ctor.name {
                    return Some(&ctor.typ);
                }
            }
        }
        return None;
    }

    fn find_class<'a>(&'a self, name: Name) -> Option<(&'a [Constraint<Name>], &'a TypeVariable, &'a [TypeDeclaration<Name>])> {
        self.classes.iter()
            .find(|class| name == class.name)
            .map(|class| (class.constraints.as_slice(), &class.variable, class.declarations.as_slice()))
    }
    fn find_instance<'a>(&'a self, classname: Name, typ: &Type) -> Option<(&'a [Constraint<Name>], &'a Type)> {
        for &(ref constraints, ref op) in self.instances.iter() {
            match op {
                &Type::Application(ref op, ref t) => {
                    let x = match extract_applied_type(*op) {
                        &Type::Constructor(ref x) => x,
                        _ => panic!()
                    };
                    let y = match extract_applied_type(*t) {
                        &Type::Constructor(ref x) => x,
                        _ => panic!()
                    };
                    let z = match extract_applied_type(typ) {
                        &Type::Constructor(ref x) => x,
                        _ => panic!()
                    };
                    if classname.name == x.name && y.name == z.name {
                        let o : &Type = *t;
                        return Some((constraints.as_slice(), o));
                    }
                }
                _ => ()
            }
        }
        None
    }
}

impl DataTypes for Assembly {
    fn find_data_type<'a>(&'a self, name: InternedStr) -> Option<&'a DataDefinition<Name>> {
        for data in self.data_definitions.iter() {
            if name == extract_applied_type(&data.typ.value).ctor().name {
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
            PushDictionary(..) | PushDictionaryMember(..) | PushBuiltin(..) => 1,
            MkapDictionary => -1,
            ConstructDictionary(size) => (size as int) - 1,
            PushDictionaryRange(..) => 1
        }
    }
}

enum ArgList<'a> {
    Cons(&'a Expr<Id>, &'a ArgList<'a>),
    Nil
}

pub struct Compiler<'a> {
    ///Hashmap containging class names mapped to the functions it contains
    pub instance_dictionaries: Vec<(Vec<(Name, Type)>, Vec<uint>)>,
    pub stackSize : uint,
    ///Array of all the assemblies which can be used to lookup functions in
    pub assemblies: Vec<&'a Assembly>,
    module: Option<&'a Module<Id>>,
    variables: ScopedMap<Name, Var<'a>>,
    context: Vec<Constraint<Name>>
}


impl <'a> Compiler<'a> {
    pub fn new() -> Compiler<'a> {
        let mut variables = ScopedMap::new();
        for (i, &(name, _)) in builtins().iter().enumerate() {
            variables.insert(Name { name: intern(name), uid: 0}, Var::Builtin(i));
        }
        for &(name, instruction) in binary_primitives.iter() {
            variables.insert(Name { name: intern(name), uid: 0 }, Var::Primitive(2, instruction));
        }
        for &(name, instruction) in unary_primitives.iter() {
            variables.insert(Name { name: intern(name), uid: 0 }, Var::Primitive(1, instruction));
        }
        Compiler { instance_dictionaries: Vec::new(),
            stackSize : 0, assemblies: Vec::new(),
            module: None,
            variables: variables,
            context: box []
        }
    }
    
    pub fn compile_module(&mut self, module : &'a Module<Id>) -> Assembly {
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
        let mut bindings = module.bindings.iter()
            .chain(module.instances.iter().flat_map(|i| i.bindings.iter()))
            .chain(module.classes.iter().flat_map(|class| class.bindings.iter()));

        for bind in bindings {
            let sc = self.compile_binding(bind);
            superCombinators.push(sc);
        }
        

        for &(_, ref dict) in self.instance_dictionaries.iter() {
            instance_dictionaries.push(dict.clone());
        }
        self.module = None;
        Assembly {
            superCombinators: superCombinators,
            instance_dictionaries: instance_dictionaries,
            offset: self.assemblies.iter().flat_map(|assembly| assembly.superCombinators.iter()).len(),
            classes: module.classes.clone(),
            instances: module.instances.iter()
                .map(|x| (x.constraints.clone(), Type::new_op(x.classname.name, box [x.typ.clone()])))
                .collect()
            ,
            data_definitions: data_definitions
        }
    }

    fn compile_binding(&mut self, bind : &Binding<Id>) -> SuperCombinator {
        debug!("Compiling binding {} :: {}", bind.name, bind.name.typ);
        let dict_arg = if bind.name.typ.constraints.len() > 0 { 1 } else { 0 };
        self.context = bind.name.typ.constraints.clone();
        let mut instructions = Vec::new();
        let mut arity = 0;
        self.scope(&mut |this| {
            if dict_arg == 1 {
                this.new_stack_var(Name { name: intern("$dict"), uid: 0 });
            }
            debug!("{} {}\n {}", bind.name, dict_arg, bind.expression);
            arity = this.compile_lambda_binding(&bind.expression, &mut instructions) + dict_arg;
            instructions.push(Update(0));
            if arity != 0 {
                instructions.push(Pop(arity));
            }
            instructions.push(Unwind);
        });
        debug!("{} :: {} compiled as:\n{}", bind.name, bind.name.typ, instructions);
        SuperCombinator {
            assembly_id: self.assemblies.len(),
            typ: bind.name.typ.clone(),
            name: bind.name.name,
            arity: arity,
            instructions: instructions
        }
    }

    fn compile_lambda_binding(&mut self, expr: &Expr<Id>, instructions: &mut Vec<Instruction>) -> uint {
        match expr {
            &Lambda(ref ident, ref body) => {
                self.new_stack_var(ident.name.clone());
                1 + self.compile_lambda_binding(*body, instructions)
            }
            _ => {
                self.compile(expr, instructions, true);
                0
            }
        }
    }
    
    ///Find a variable by walking through the stack followed by all globals
    fn find(&self, identifier : Name) -> Option<Var<'a>> {
        self.variables.find(&identifier).map(|x| x.clone())
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
            Compiler::find_builtin_constructor(identifier.name)
                .map(|(x, y)| Var::Constructor(x, y))
        })
    }

    fn find_constructor(&self, identifier : Name) -> Option<(u16, u16)> {
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
            Compiler::find_builtin_constructor(identifier.name)
        })
    }

    fn find_builtin_constructor(identifier: InternedStr) -> Option<(u16, u16)> {
        let identifier = identifier.as_slice();
        if identifier.len() >= 2 && identifier.char_at(0) == '('
        && identifier.char_at(identifier.len() - 1) == ')'
        && identifier.chars().skip(1).take(identifier.len() - 2).all(|c| c == ',') {
            let num_args =
                if identifier.len() == 2 { 0 }//unit
                else { identifier.len() - 1 };//tuple
            return Some((0, num_args as u16));
        }
        match identifier {
            "[]" => Some((0, 0)),
            ":" => Some((1, 2)),
            _ => None
        }
    }

    fn find_class<'a>(&'a self, name: Name) -> Option<(&'a [Constraint<Name>], &'a TypeVariable, &'a [TypeDeclaration<Name>])> {
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

    fn new_stack_var(&mut self, identifier : Name) {
        self.variables.insert(identifier, Var::Stack(self.stackSize));
        self.stackSize += 1;
    }
    fn new_var_at(&mut self, identifier : Name, index: uint) {
        self.variables.insert(identifier, Var::Stack(index));
    }

    fn scope(&mut self, f: &mut FnMut(&mut Compiler)) {
        self.variables.enter_scope();
        let stackSize = self.stackSize;
        f(self);
        self.stackSize = stackSize;
        self.variables.exit_scope();
    }

    ///Compile an expression by appending instructions to the instruction vector
    fn compile(&mut self, expr : &Expr<Id>, instructions : &mut Vec<Instruction>, strict: bool) {
        match expr {
            &Identifier(_) => {
                self.compile_apply(expr, ArgList::Nil, instructions, strict);
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
                                name: Name { name: intern("fromInteger"), uid: 0 }, 
                                typ: qualified(vec![], function_type_(int_type(), literal.typ.clone())),
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
                                name: Name { name: intern("fromRational"), uid: 0 }, 
                                typ: qualified(vec![], function_type_(double_type(), literal.typ.clone())),
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
            &Apply(..) => {
                self.compile_apply(expr, ArgList::Nil, instructions, strict);
            }
            &Let(ref bindings, ref body) => {
                self.scope(&mut |this| {
                    for bind in bindings.iter() {
                        this.new_stack_var(bind.name.name.clone());
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

                    self.scope(&mut |this| {
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
            &Lambda(_, _) => panic!("Error: Found non-lifted lambda when compiling expression")
        }
    }
    fn compile_apply<'a>(&mut self, expr: &Expr<Id>, args: ArgList<'a>, instructions: &mut Vec<Instruction>, strict: bool) {
        //Unroll the applications until the function is found
        match *expr {
            Apply(ref func, ref arg) => {
                return self.compile_apply(*func, ArgList::Cons(*arg, &args), instructions, strict)
            }
            _ => ()
        }
        //Tracks if the application is a regular function in which case we need to add Mkap instructions at the end
        let mut is_function = true;
        let arg_length;
        match *expr {
            Identifier(ref name) => {
                //When compiling a variable which has constraints a new instance dictionary
                //might be created which is returned here and added to the assembly
                let mut is_primitive = false;
                let var = self.find(name.name)
                    .unwrap_or_else(|| panic!("Error: Undefined variable {}", *name));
                match var {
                    Var::Primitive(..) => is_primitive = true,
                    _ => ()
                }
                arg_length = self.compile_args(&args, instructions, is_primitive);
                match var {
                    Var::Stack(index) => { instructions.push(Push(index)); }
                    Var::Global(index) => { instructions.push(PushGlobal(index)); }
                    Var::Constructor(tag, arity) => {
                        instructions.push(Pack(tag, arity));
                        is_function = false;
                    }
                    Var::Builtin(index) => { instructions.push(PushBuiltin(index)); }
                    Var::Class(typ, constraints, var) => {
                        debug!("Var::Class ({}, {}, {}) {}", typ, constraints, var, expr.get_type());
                        self.compile_instance_variable(expr.get_type(), instructions, name.name, typ, constraints, var);
                    }
                    Var::Constraint(index, bind_type, constraints) => {
                        debug!("Var::Constraint {} ({}, {}, {})", name, index, bind_type, constraints);
                        self.compile_with_constraints(name.name, expr.get_type(), bind_type, constraints, instructions);
                        instructions.push(PushGlobal(index));
                        instructions.push(Mkap);
                    }
                    Var::Primitive(num_args, instruction) => {
                        if num_args == arg_length {
                            instructions.push(instruction);
                        }
                        else {
                            panic!("Expected {} arguments for {}, got {}", num_args, name, arg_length)
                        }
                        is_function = false;
                    }
                    Var::Newtype => {
                        match args {
                            ArgList::Cons(_, _) => {
                                //Do nothing
                            }
                            Nil => {
                                //translate into id application
                                let x = self.find(Name { name: intern("id"), uid: 0 })
                                    .expect("Compiler error: Prelude.id must be in scope for compilation of newtype");
                                match x {
                                    Var::Global(index) => {
                                        instructions.push(PushGlobal(index));
                                    }
                                    _ => panic!()
                                }
                            }
                        }
                        is_function = false;
                    }
                }
            }
            _ => {
                arg_length = self.compile_args(&args, instructions, strict);
                self.compile(expr, instructions, strict);
            }
        }
        self.stackSize -= arg_length;
        if is_function {
            for _ in range(0, arg_length) {
                instructions.push(Mkap);
            }
            if strict {
                instructions.push(Eval);
            }
        }
    }

    fn compile_args<'a>(&mut self, args: &ArgList<'a>, instructions: &mut Vec<Instruction>, strict: bool) -> uint {
        match *args {
            ArgList::Cons(arg, rest) => {
                let i = self.compile_args(rest, instructions, strict);
                //The stack has increased by 1 until the function compiles and reduces it wtih Pack or Mkap
                self.compile(arg, instructions, strict);
                self.stackSize += 1;
                i + 1
            }
            ArgList::Nil => 0
        }
    }

    ///Compile a function which is defined in a class
    fn compile_instance_variable(&mut self, actual_type: &Type, instructions: &mut Vec<Instruction>, name: Name, function_type: &Type, constraints: &[Constraint<Name>], var: &TypeVariable) {
        match try_find_instance_type(var, function_type, actual_type) {
            Some(typename) => {
                //We should be able to retrieve the instance directly
                let mut b = "#".to_string();
                b.push_str(typename);
                b.push_str(name.as_slice());
                let instance_fn_name = Name { name: intern(b.as_slice()), uid: name.uid };
                match self.find(instance_fn_name) {
                    Some(Var::Global(index)) => {
                        instructions.push(PushGlobal(index));
                    }
                    Some(Var::Constraint(index, function_type, constraints)) => {
                        self.compile_with_constraints(instance_fn_name, actual_type, function_type, constraints, instructions);
                        instructions.push(PushGlobal(index));
                        instructions.push(Mkap);
                    }
                    _ => panic!("Unregistered instance function {}", instance_fn_name)
                }
            }
            None => {
                self.compile_with_constraints(name, actual_type, function_type, constraints, instructions)
            }
        }
    }

    ///Compile the loading of a variable which has constraints and will thus need to load a dictionary with functions as well
    fn compile_with_constraints(&mut self, name: Name, actual_type: &Type, function_type: &Type, constraints: &[Constraint<Name>], instructions: &mut Vec<Instruction>) {
        match self.find(Name { name: intern("$dict"), uid: 0}) {
            Some(Var::Stack(_)) => {
                //Push dictionary or member of dictionary
                match self.push_dictionary_member(constraints, name) {
                    Some(index) => instructions.push(PushDictionaryMember(index)),
                    None => {
                        let dictionary_key = find_specialized_instances(function_type, actual_type, constraints);
                        self.push_dictionary(constraints, dictionary_key, instructions);
                    }
                }
            }
            _ => {
                //get dictionary index
                //push dictionary
                let dictionary_key = find_specialized_instances(function_type, actual_type, constraints);
                self.push_dictionary(constraints, dictionary_key, instructions);
            }
        }
    }
    
    fn push_dictionary(&mut self, context: &[Constraint<Name>], constraints: &[(Name, Type)], instructions: &mut Vec<Instruction>) {
        debug!("Push dictionary {} ==> {}", context, constraints);
        for &(ref class, ref typ) in constraints.iter() {
            self.fold_dictionary(*class, typ, instructions);
            instructions.push(ConstructDictionary(constraints.len()));
        }
    }
    
    //Writes instructions which pushes a dictionary for the type to the top of the stack
    fn fold_dictionary(&mut self, class: Name, typ: &Type, instructions: &mut Vec<Instruction>) {
        match *typ {
            Type::Constructor(ref ctor) => {//Simple
                debug!("Simple for {}", ctor);
                //Push static dictionary to the top of the stack
                let index = self.find_dictionary_index(&[(class.clone(), typ.clone())]);
                instructions.push(PushDictionary(index));
            }
            Type::Application(ref lhs, ref rhs) => {
                debug!("App for ({} {})", lhs, rhs);
                //For function in functions
                // Mkap function fold_dictionary(rhs)
                self.fold_dictionary(class, *lhs, instructions);
                self.fold_dictionary(class, *rhs, instructions);
                instructions.push(MkapDictionary);
            }
            Type::Variable(ref var) => {
                //This variable must appear in the context
                let mut has_constraint = false;
                let mut index = 0;
                for constraint in self.context.iter() {
                    if constraint.variables[0] == *var && constraint.class == class {
                        has_constraint = true;
                        break
                    }
                    let (_, _, decls) = self.find_class(constraint.class).unwrap();
                    index += decls.len();
                }
                if has_constraint {
                    //Found the variable in the constraints
                    let num_class_functions = self.find_class(class)
                        .map(|(_, _, decls)| decls.len())
                        .unwrap();
                    debug!("Use previous dict for {} at {}..{}", var, index, num_class_functions);
                    instructions.push(PushDictionaryRange(index, num_class_functions));
                }
                else {
                    debug!("No dict for {}", var);
                }
            }
            _ => panic!("Did not expect generic")
        }
    }

    ///Lookup which index in the instance dictionary that holds the function called 'name'
    fn push_dictionary_member(&self, constraints: &[Constraint<Name>], name: Name) -> Option<uint> {
        if constraints.len() == 0 {
            panic!("Attempted to push dictionary member '{}' with no constraints", name)
        }
        let mut ii = 0;
        for c in constraints.iter() {
            let result = self.walk_classes(c.class, &mut |declarations| {
                for decl in declarations.iter() {
                    if decl.name == name {
                        return Some(ii)
                    }
                    ii += 1;
                }
                None
            });
            if result.is_some() {
                return result;
            }
        }
        None
    }

    ///Walks through the class and all of its super classes, calling 'f' on each of them
    ///Returning Some(..) from the function quits and returns that value
    fn walk_classes<T>(&self, class: Name, f: &mut FnMut(&[TypeDeclaration<Name>]) -> Option<T>) -> Option<T> {
        let (constraints, _, declarations) = self.find_class(class)
            .expect("Compiler error: Expected class");
        //Look through the functions in any super classes first
        constraints.iter()
            .filter_map(|constraint| self.walk_classes(constraint.class, f))
            .next()
            .or_else(|| (*f)(declarations))
    }

    ///Find the index of the instance dictionary for the constraints and types in 'constraints'
    ///Returns the index
    fn find_dictionary_index(&mut self, constraints: &[(Name, Type)]) -> uint {
        //Check if the dictionary already exist
        let dict_len = self.instance_dictionaries.len();
        for ii in range(0, dict_len) {
            if self.instance_dictionaries.get(ii).ref0().equiv(&constraints) {
                return ii;
            }
        }

        if constraints.len() == 0 {
            panic!("Error: Attempted to compile dictionary with no constraints at <unknown>");
        }
        let mut function_indexes = Vec::new();
        self.add_class(constraints, &mut function_indexes);
        self.instance_dictionaries.push((constraints.to_owned(), function_indexes));
        dict_len
    }

    fn add_class(&self, constraints: &[(Name, Type)], function_indexes: &mut Vec<uint>) {

        fn extract_applied_type<'a>(typ: &'a Type) -> &'a Type {
            match typ {
                &Type::Application(ref lhs, _) => extract_applied_type(*lhs),
                _ => typ
            }
        }

        for &(ref class_name, ref typ) in constraints.iter() {
            self.walk_classes(*class_name, &mut |declarations| -> Option<()> {
                for decl in declarations.iter() {
                    let x = match extract_applied_type(typ) {
                        &Type::Constructor(ref x) => x,
                        _ => panic!("{}", typ)
                    };
                    let mut b = "#".to_string();
                    b.push_str(x.name.as_slice());
                    b.push_str(decl.name.as_slice());
                    let f = intern(b.as_slice());
                    let name = Name { name: f, uid: decl.name.uid };
                    match self.find(name) {
                        Some(Var::Global(index)) => {
                            function_indexes.push(index as uint);
                        }
                        Some(Var::Constraint(index, _, _)) => {
                            function_indexes.push(index as uint);//TODO this is not really correct since this function requires a dictionary
                        }
                        var => panic!("Did not find function {} {}", name, var)
                    }
                }
                None
            });
        }
    }

    ///Compiles a pattern.
    ///An index to the Jump instruction which is taken when the match fails is stored in the branches vector
    ///These instructions will need to be updated later with the correct jump location.
    fn compile_pattern(&mut self, pattern: &Pattern<Id>, branches: &mut Vec<uint>, instructions: &mut Vec<Instruction>, stack_size: uint) -> uint {
        debug!("Pattern {} at {}", pattern, stack_size);
        match pattern {
            &Pattern::Constructor(ref name, ref patterns) => {
                instructions.push(Push(stack_size));
                match self.find_constructor(name.name) {
                    Some((tag, _)) => {
                        instructions.push(CaseJump(tag as uint));
                        branches.push(instructions.len());
                        instructions.push(Jump(0));
                    }
                    _ => panic!("Undefined constructor {}", *name)
                }
                instructions.push(Split(patterns.len()));
                self.stackSize += patterns.len();
                for (i, p) in patterns.iter().enumerate() {
                    self.new_var_at(p.name.clone(), self.stackSize - patterns.len() + i);
                }
                patterns.len()
            }
            &Pattern::Number(number) => {
                instructions.push(Push(stack_size));
                instructions.push(Eval);
                instructions.push(PushInt(number));
                instructions.push(IntEQ);
                instructions.push(JumpFalse(0));
                0
            }
            &Pattern::Identifier(ref ident) => {
                self.new_var_at(ident.name.clone(), stack_size);
                0
            }
            &Pattern::WildCard => {
                0
            }
        }
    }
}

///Attempts to find the actual type of the for the variable which has a constraint
fn try_find_instance_type<'a>(class_var: &TypeVariable, class_type: &Type, actual_type: &'a Type) -> Option<&'a str> {
    match (class_type, actual_type) {
        (&Type::Variable(ref var), _) if var == class_var => {
            //Found the class variable so return the name of the type
            match extract_applied_type(actual_type) {
                &Type::Constructor(ref op) => { Some(op.name.as_slice()) }
                _ => None
            }
        }
        (&Type::Constructor(ref class_op), &Type::Constructor(ref actual_op)) => {
            assert_eq!(class_op.name, actual_op.name);
            None
        }
        (&Type::Application(ref lhs1, ref rhs1), &Type::Application(ref lhs2, ref rhs2)) => {
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
    let mut compiler = Compiler::new();
    for assem in assemblies.iter() {
        compiler.assemblies.push(*assem);
    }
    compiler.compile_module(&core_module)
}

pub fn compile_string(module: &str) -> IoResult<Vec<Assembly>> {
    use typecheck::typecheck_string;
    let modules = try!(typecheck_string(module));
    compile_module_(modules)
}

///Takes a module name and does everything needed up to and including compiling the module
///and its imported modules
pub fn compile_module(module: &str) -> IoResult<Vec<Assembly>> {
    use typecheck::typecheck_module;
    let modules = try!(typecheck_module(module));
    compile_module_(modules)
}

fn compile_module_(modules: Vec<::module::Module<Name>>) -> IoResult<Vec<Assembly>> {
    use compiler::Compiler;
    let core_modules: Vec<Module<Id<Name>>> = translate_modules(modules)
        .into_iter()
        .map(|module| do_lambda_lift(module))
        .collect();
    let mut assemblies = Vec::new();
    for module in core_modules.iter() {
        let x = {
            let mut compiler = Compiler::new();
            for a in assemblies.iter() {
                compiler.assemblies.push(a);
            }
            compiler.compile_module(module)
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

    assert_eq!(assembly.superCombinators[0].instructions, vec![PushInt(2), PushInt(1), Add, Update(0), Unwind]);
}

#[test]
fn add_double() {
    let file =
r"add x y = primDoubleAdd x y
main = add 2. 3.";
    let assembly = compile(file);

    assert_eq!(assembly.superCombinators[0].instructions, vec![Push(1), Eval, Push(0), Eval, DoubleAdd, Update(0), Pop(2), Unwind]);
    assert_eq!(assembly.superCombinators[1].instructions, vec![PushFloat(3.), PushFloat(2.), PushGlobal(0), Mkap, Mkap, Eval, Update(0), Unwind]);
}
#[test]
fn push_num_double() {
    let file =
r"main = primDoubleAdd 2 3";
    let assembly = compile(file);

    assert_eq!(assembly.superCombinators[0].instructions, vec![PushFloat(3.), PushFloat(2.), DoubleAdd, Update(0), Unwind]);
}

#[test]
fn application() {
    let file =
r"add x y = primIntAdd x y
main = add 2 3";
    let assembly = compile(file);

    assert_eq!(assembly.superCombinators[1].instructions, vec![PushInt(3), PushInt(2), PushGlobal(0), Mkap, Mkap, Eval, Update(0), Unwind]);
}

#[test]
fn compile_constructor() {
    let file =
r"main = primIntAdd 1 0 : []";
    let assembly = compile(file);

    assert_eq!(assembly.superCombinators[0].instructions, vec![Pack(0, 0), PushInt(0), PushInt(1), Add, Pack(1, 2), Update(0), Unwind]);
}

#[test]
fn compile_tuple() {
    let file =
r"test x y = (primIntAdd 0 1, x, y)";
    let assembly = compile(file);

    assert_eq!(assembly.superCombinators[0].instructions, vec![Push(1), Push(0), PushInt(1), PushInt(0), Add, Pack(0, 3), Update(0), Pop(2), Unwind]);
}

#[test]
fn compile_case() {
    let file =
r"main = case [primIntAdd 1 0] of
    x:xs -> x
    [] -> 2";
    let assembly = compile(file);


    assert_eq!(assembly.superCombinators[0].instructions, vec![Pack(0, 0), PushInt(0), PushInt(1), Add, Pack(1, 2),
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

    let main = &assembly.superCombinators[0];
    assert_eq!(main.name.name, intern("main"));
    assert_eq!(main.instructions, vec![PushInt(0), PushInt(6), Add, PushGlobal(1), Mkap, Eval, Update(0), Unwind]);
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

    let main = assembly.superCombinators[0];
    assert_eq!(main.name.name, intern("main"));
    assert_eq!(main.instructions, vec![PushInt(6), Push(1), PushDictionaryMember(0), Mkap, Eval, Add, Update(0), Pop(2), Unwind]);
}

#[test]
fn compile_prelude() {
    let mut type_env = TypeEnvironment::new();
    let prelude = compile_with_type_env(&mut type_env, [], File::open(&Path::new("Prelude.hs")).read_to_str().unwrap().as_slice());

    let assembly = compile_with_type_env(&mut type_env, [&prelude], r"main = id (primIntAdd 2 0)");

    let sc = &assembly.superCombinators[0];
    let id_index = prelude.superCombinators.iter().position(|sc| sc.name.name == intern("id")).unwrap();
    assert_eq!(sc.instructions, vec![PushInt(0), PushInt(2), Add, PushGlobal(id_index), Mkap, Eval, Update(0), Unwind]);
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

#[test]
fn newtype() {
    //Test that the newtype constructor is newer constucted
    let file =
r"
newtype Test a = Test [a]
test = Test [1::Int]";
    let assembly = compile(file);

    let test = assembly.superCombinators[0];
    assert_eq!(test.instructions, box [Pack(0, 0), PushInt(1), Pack(1, 2), Update(0), Unwind]);
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
        let mut compiler = Compiler::new();
        compiler.compile_module(&core_module)
    });
}
}
