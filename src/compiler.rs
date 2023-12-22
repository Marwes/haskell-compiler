use {
    crate::{
        core::{
            Expr::*,
            *,
        },
        interner::*,
        scoped_map::ScopedMap,
        typecheck::{
            find_specialized_instances,
            DataTypes,
            TypeEnvironment,
            Types,
        },
        types::{
            extract_applied_type,
            qualified,
        },
    },
    std::borrow::ToOwned,
};

use crate::{
    builtins::builtins,
    core::translate::{
        translate_module,
        translate_modules,
    },
    lambda_lift::do_lambda_lift,
    renamer::{
        rename_module,
        typ::*,
    },
};

use self::Instruction::*;

#[derive(PartialEq, Clone, Copy, Debug)]
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
    Push(usize),
    PushGlobal(usize),
    PushInt(isize),
    PushFloat(f64),
    PushChar(char),
    Mkap,
    Eval,
    Unwind,
    Update(usize),
    Pop(usize),
    Slide(usize),
    Split(usize),
    Pack(u16, u16),
    CaseJump(usize),
    Jump(usize),
    JumpFalse(usize),
    PushDictionary(usize),
    PushDictionaryMember(usize),
    PushBuiltin(usize),
    MkapDictionary,
    ConstructDictionary(usize),
    PushDictionaryRange(usize, usize),
}
#[derive(Debug)]
enum Var<'a> {
    Stack(usize),
    Global(usize),
    Constructor(u16, u16),
    Class(&'a Type<Name>, &'a [Constraint<Name>], &'a TypeVariable),
    Constraint(usize, &'a Type<Name>, &'a [Constraint<Name>]),
    Builtin(usize),
    Primitive(usize, Instruction),
    Newtype,
}

static UNARY_PRIMITIVES: &'static [(&'static str, Instruction)] = &[
    ("primIntToDouble", IntToDouble),
    ("primDoubleToInt", DoubleToInt),
];

static BINARY_PRIMITIVES: &'static [(&'static str, Instruction)] = &[
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

impl<'a> Clone for Var<'a> {
    fn clone(&self) -> Self {
        match *self {
            Self::Stack(x) => Self::Stack(x),
            Self::Global(x) => Self::Global(x),
            Self::Constructor(x, y) => Self::Constructor(x, y),
            Self::Class(x, y, z) => Self::Class(x, y, z),
            Self::Constraint(x, y, z) => Self::Constraint(x, y, z),
            Self::Builtin(x) => Self::Builtin(x),
            Self::Primitive(x, y) => Self::Primitive(x, y),
            Self::Newtype => Self::Newtype,
        }
    }
}

pub struct SuperCombinator {
    pub arity: usize,
    pub name: Name,
    pub assembly_id: usize,
    pub instructions: Vec<Instruction>,
    pub typ: Qualified<Type<Name>, Name>,
}
pub struct Assembly {
    pub super_combinators: Vec<SuperCombinator>,
    pub instance_dictionaries: Vec<Vec<usize>>,
    pub classes: Vec<Class<Id>>,
    pub instances: Vec<(Vec<Constraint<Name>>, Type<Name>)>,
    pub data_definitions: Vec<DataDefinition<Name>>,
    pub offset: usize,
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
                    return Some(
                        Var::Class(&decl.typ.value, &*decl.typ.constraints, &class.variable)
                    );
                }
            }
        }

        let mut index = 0;
        for sc in self.super_combinators.iter() {
            if name == sc.name {
                if sc.typ.constraints.len() > 0 {
                    return Some(
                        Var::Constraint(self.offset + index, &sc.typ.value, &*sc.typ.constraints)
                    );
                } else {
                    return Some(Var::Global(self.offset + index));
                }
            }
            index += 1;
        }
        self.find_constructor(name)
            .map(|(tag, arity)| Var::Constructor(tag, arity))
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

fn find_global<'a>(module: &'a Module<Id>, offset: usize, name: Name) -> Option<Var<'a>> {
    for class in module.classes.iter() {
        for decl in class.declarations.iter() {
            if decl.name == name {
                return Some(Var::Class(&decl.typ.value, &*decl.typ.constraints, &class.variable));
            }
        }
    }

    let mut global_index = 0;
    module
        .bindings
        .iter()
        .chain(
            module
                .instances
                .iter()
                .flat_map(|instance| instance.bindings.iter()),
        )
        .chain(module.classes.iter().flat_map(|c| c.bindings.iter()))
        .find(|bind| {
            global_index += 1;
            bind.name.name == name
        })
        .map(|bind| {
            global_index -= 1;
            let typ = bind.expression.get_type();
            let constraints = &bind.name.typ.constraints;
            if constraints.len() > 0 {
                Var::Constraint(offset + global_index, typ, &**constraints)
            } else {
                Var::Global(offset + global_index)
            }
        })
        .or_else(|| {
            module
                .newtypes
                .iter()
                .find(|newtype| newtype.constructor_name == name)
                .map(|_| Var::Newtype)
        })
        .or_else(|| find_constructor(module, name).map(|(tag, arity)| Var::Constructor(tag, arity)))
}

fn find_constructor(module: &Module<Id>, name: Name) -> Option<(u16, u16)> {
    for data_def in module.data_definitions.iter() {
        for ctor in data_def.constructors.iter() {
            if name == ctor.name {
                return Some((ctor.tag as u16, ctor.arity as u16));
            }
        }
    }
    None
}

impl Types for Module<Id> {
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Qualified<Type<Name>, Name>> {
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
        self.newtypes
            .iter()
            .find(|newtype| newtype.constructor_name == *name)
            .map(|newtype| &newtype.constructor_type)
    }

    fn find_class<'a>(
        &'a self,
        name: Name,
    ) -> Option<(
        &'a [Constraint<Name>],
        &'a TypeVariable,
        &'a [TypeDeclaration<Name>],
    )> {
        self.classes
            .iter()
            .find(|class| name == class.name)
            .map(|class| {
                (
                    class.constraints.as_ref(),
                    &class.variable,
                    class.declarations.as_ref(),
                )
            })
    }

    fn find_instance<'a>(
        &'a self,
        classname: Name,
        typ: &Type<Name>,
    ) -> Option<(&'a [Constraint<Name>], &'a Type<Name>)> {
        for instance in self.instances.iter() {
            let y = match extract_applied_type(&instance.typ) {
                &Type::Constructor(ref x) => x,
                _ => panic!(),
            };
            let z =
                match extract_applied_type(typ) {
                    &Type::Constructor(ref x) => x,
                    _ => panic!(),
                };
            if classname == instance.classname && y.name == z.name {
                return Some((instance.constraints.as_ref(), &instance.typ));
            }
        }
        None
    }
}

impl Types for Assembly {
    ///Lookup a type
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Qualified<Type<Name>, Name>> {
        for sc in self.super_combinators.iter() {
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

    fn find_class<'a>(
        &'a self,
        name: Name,
    ) -> Option<(
        &'a [Constraint<Name>],
        &'a TypeVariable,
        &'a [TypeDeclaration<Name>],
    )> {
        self.classes
            .iter()
            .find(|class| name == class.name)
            .map(|class| {
                (
                    class.constraints.as_ref(),
                    &class.variable,
                    class.declarations.as_ref(),
                )
            })
    }
    fn find_instance<'a>(
        &'a self,
        classname: Name,
        typ: &Type<Name>,
    ) -> Option<(&'a [Constraint<Name>], &'a Type<Name>)> {
        for &(ref constraints, ref op) in self.instances.iter() {
            match op {
                &Type::Application(ref op, ref t) => {
                    let x = match extract_applied_type(&**op) {
                        &Type::Constructor(ref x) => x,
                        _ => panic!(),
                    };
                    let y = match extract_applied_type(&**t) {
                        &Type::Constructor(ref x) => x,
                        _ => panic!(),
                    };
                    let z = match extract_applied_type(typ) {
                        &Type::Constructor(ref x) => x,
                        _ => panic!(),
                    };
                    if classname.name == x.name && y.name == z.name {
                        return Some((constraints.as_ref(), &**t));
                    }
                }
                _ => (),
            }
        }
        None
    }
}

impl DataTypes for Assembly {
    fn find_data_type<'a>(&'a self, name: Name) -> Option<&'a DataDefinition<Name>> {
        for data in self.data_definitions.iter() {
            if name == extract_applied_type(&data.typ.value).ctor().name {
                return Some(data);
            }
        }
        None
    }
}

enum ArgList<'a> {
    Cons(&'a Expr<Id>, &'a ArgList<'a>),
    Nil,
}

pub struct Compiler<'a> {
    ///Hashmap containging class names mapped to the functions it contains
    pub instance_dictionaries: Vec<(Vec<(Name, Type<Name>)>, Vec<usize>)>,
    pub stack_size: usize,
    ///Array of all the assemblies which can be used to lookup functions in
    pub assemblies: Vec<&'a Assembly>,
    module: Option<&'a Module<Id>>,
    variables: ScopedMap<Name, Var<'a>>,
    context: Vec<Constraint<Name>>,
}

impl<'a> Compiler<'a> {
    pub fn new() -> Self {
        let mut variables = ScopedMap::new();
        for (i, &(name, _)) in builtins().iter().enumerate() {
            variables.insert(
                Name {
                    name: intern(name),
                    uid: 0,
                },
                Var::Builtin(i),
            );
        }
        for &(name, instruction) in BINARY_PRIMITIVES.iter() {
            variables.insert(
                Name {
                    name: intern(name),
                    uid: 0,
                },
                Var::Primitive(2, instruction),
            );
        }
        for &(name, instruction) in UNARY_PRIMITIVES.iter() {
            variables.insert(
                Name {
                    name: intern(name),
                    uid: 0,
                },
                Var::Primitive(1, instruction),
            );
        }
        Self {
            instance_dictionaries: vec![],
            stack_size: 0,
            assemblies: vec![],
            module: None,
            variables,
            context: vec![],
        }
    }

    pub fn compile_module(&mut self, module: &'a Module<Id>) -> Assembly {
        self.module = Some(module);
        let mut super_combinators = vec![];
        let mut instance_dictionaries = vec![];
        let mut data_definitions = vec![];

        for def in module.data_definitions.iter() {
            let mut constructors = vec![];
            for ctor in def.constructors.iter() {
                constructors.push(ctor.clone());
            }
            data_definitions.push(def.clone());
        }
        let bindings = module
            .bindings
            .iter()
            .chain(module.instances.iter().flat_map(|i| i.bindings.iter()))
            .chain(
                module
                    .classes
                    .iter()
                    .flat_map(|class| class.bindings.iter()),
            );

        for bind in bindings {
            let sc = self.compile_binding(bind);
            super_combinators.push(sc);
        }

        for &(_, ref dict) in self.instance_dictionaries.iter() {
            instance_dictionaries.push(dict.clone());
        }
        self.module = None;
        Assembly {
            super_combinators,
            instance_dictionaries,
            offset: self
                .assemblies
                .iter()
                .fold(0, |sum, assembly| sum + assembly.super_combinators.len()),
            classes: module.classes.clone(),
            instances: module
                .instances
                .iter()
                .map(|x| {
                    (
                        x.constraints.clone(),
                        Type::new_op(x.classname, vec![x.typ.clone()]),
                    )
                })
                .collect(),
            data_definitions,
        }
    }

    fn compile_binding(&mut self, bind: &Binding<Id>) -> SuperCombinator {
        debug!("Compiling binding {:?} :: {:?}", bind.name, bind.name.typ);
        let dict_arg = if bind.name.typ.constraints.len() > 0 {
            1
        } else {
            0
        };
        self.context = bind.name.typ.constraints.clone();
        let mut instructions = vec![];
        let mut arity = 0;
        self.scope(&mut |this| {
            if dict_arg == 1 {
                this.new_stack_var(Name {
                    name: intern("$dict"),
                    uid: 0,
                });
            }
            debug!("{:?} {:?}\n {:?}", bind.name, dict_arg, bind.expression);
            arity = this.compile_lambda_binding(&bind.expression, &mut instructions) + dict_arg;
            instructions.push(Update(0));
            if arity != 0 {
                instructions.push(Pop(arity));
            }
            instructions.push(Unwind);
        });
        debug!(
            "{:?} :: {:?} compiled as:\n{:?}",
            bind.name, bind.name.typ, instructions
        );
        SuperCombinator {
            assembly_id: self.assemblies.len(),
            typ: bind.name.typ.clone(),
            name: bind.name.name,
            arity,
            instructions,
        }
    }

    fn compile_lambda_binding(
        &mut self,
        expr: &Expr<Id>,
        instructions: &mut Vec<Instruction>,
    ) -> usize {
        match expr {
            &Lambda(ref ident, ref body) => {
                self.new_stack_var(ident.name.clone());
                1 + self.compile_lambda_binding(&**body, instructions)
            }
            _ => {
                self.compile(expr, instructions, true);
                0
            }
        }
    }

    ///Find a variable by walking through the stack followed by all globals
    fn find(&self, identifier: Name) -> Option<Var<'a>> {
        self.variables
            .find(&identifier)
            .map(|x| x.clone())
            .or_else(|| match self.module {
                Some(ref module) => {
                    let n = self.assemblies.len();
                    let offset = if n > 0 {
                        let assembly = self.assemblies[n - 1];
                        assembly.offset + assembly.super_combinators.len()
                    } else {
                        0
                    };
                    find_global(*module, offset, identifier)
                }
                None => None,
            })
            .or_else(|| {
                for assembly in self.assemblies.iter() {
                    match assembly.find_global(identifier) {
                        Some(var) => return Some(var),
                        None => (),
                    }
                }
                None
            })
            .or_else(|| {
                Compiler::find_builtin_constructor(identifier.name)
                    .map(|(x, y)| Var::Constructor(x, y))
            })
    }

    fn find_constructor(&self, identifier: Name) -> Option<(u16, u16)> {
        self.module
            .and_then(|module| find_constructor(module, identifier))
            .or_else(|| {
                for assembly in self.assemblies.iter() {
                    match assembly.find_constructor(identifier) {
                        Some(var) => return Some(var),
                        None => (),
                    }
                }
                None
            })
            .or_else(|| Compiler::find_builtin_constructor(identifier.name))
    }

    fn find_builtin_constructor(identifier: InternedStr) -> Option<(u16, u16)> {
        let identifier = identifier.as_ref();
        if identifier.len() >= 2
            && identifier.starts_with('(')
            && identifier.ends_with(')')
            && identifier
                .chars()
                .skip(1)
                .take(identifier.len() - 2)
                .all(|c| c == ',')
        {
            let num_args = if identifier.len() == 2 {
                0
            }
            //unit
            else {
                identifier.len() - 1
            }; //tuple
            return Some((0, num_args as u16));
        }
        match identifier {
            "[]" => Some((0, 0)),
            ":" => Some((1, 2)),
            _ => None,
        }
    }

    fn find_class(
        &self,
        name: Name,
    ) -> Option<(&[Constraint<Name>], &TypeVariable, &[TypeDeclaration<Name>])> {
        self.module.and_then(|m| m.find_class(name)).or_else(|| {
            for types in self.assemblies.iter() {
                match types.find_class(name) {
                    Some(result) => return Some(result),
                    None => (),
                }
            }
            None
        })
    }

    fn new_stack_var(&mut self, identifier: Name) {
        self.variables
            .insert(identifier, Var::Stack(self.stack_size));
        self.stack_size += 1;
    }
    fn new_var_at(&mut self, identifier: Name, index: usize) {
        self.variables.insert(identifier, Var::Stack(index));
    }

    fn scope(&mut self, f: &mut dyn FnMut(&mut Compiler)) {
        self.variables.enter_scope();
        let stack_size = self.stack_size;
        f(self);
        self.stack_size = stack_size;
        self.variables.exit_scope();
    }

    ///Compile an expression by appending instructions to the instruction vector
    fn compile(&mut self, expr: &Expr<Id>, instructions: &mut Vec<Instruction>, strict: bool) {
        match expr {
            &Identifier(_) => {
                self.compile_apply(expr, ArgList::Nil, instructions, strict);
            }
            &Literal(ref literal) => match &literal.value {
                &Integral(i) => {
                    if literal.typ == int_type() {
                        instructions.push(PushInt(i));
                    } else if literal.typ == double_type() {
                        instructions.push(PushFloat(i as f64));
                    } else {
                        let from_integer = Identifier(Id {
                            name: Name {
                                name: intern("fromInteger"),
                                uid: 0,
                            },
                            typ: qualified(vec![], function_type_(int_type(), literal.typ.clone())),
                        });
                        let number = Literal(LiteralData {
                            typ: int_type(),
                            value: Integral(i),
                        });
                        let apply = Apply(Box::new(from_integer), Box::new(number));
                        self.compile(&apply, instructions, strict);
                    }
                }
                &Fractional(f) => {
                    if literal.typ == double_type() {
                        instructions.push(PushFloat(f));
                    } else {
                        let from_rational = Identifier(Id {
                            name: Name {
                                name: intern("fromRational"),
                                uid: 0,
                            },
                            typ: qualified(
                                vec![],
                                function_type_(double_type(), literal.typ.clone()),
                            ),
                        });
                        let number = Literal(LiteralData {
                            typ: double_type(),
                            value: Fractional(f),
                        });
                        let apply = Apply(Box::new(from_rational), Box::new(number));
                        self.compile(&apply, instructions, strict);
                    }
                }
                &String(ref s) => {
                    instructions.push(Pack(0, 0));
                    for c in s.as_ref().chars().rev() {
                        instructions.push(PushChar(c));
                        instructions.push(Pack(1, 2));
                    }
                }
                &Char(c) => instructions.push(PushChar(c)),
            },
            &Apply(..) => {
                self.compile_apply(expr, ArgList::Nil, instructions, strict);
            }
            &Let(ref bindings, ref body) => {
                self.scope(&mut |this| {
                    for bind in bindings.iter() {
                        this.new_stack_var(bind.name.name.clone());
                        //Workaround since this compiles non-recursive bindings
                        //The stack is not actually increased until after the binding is compiled
                        this.stack_size -= 1;
                        this.compile(&bind.expression, instructions, false);
                        this.stack_size += 1;
                    }
                    this.compile(&**body, instructions, strict);
                    instructions.push(Slide(bindings.len()));
                });
            }
            &Case(ref body, ref alternatives) => {
                self.compile(&**body, instructions, true);
                self.stack_size += 1;
                //Dummy variable for the case expression
                //Storage for all the jumps that should go to the end of the case expression
                let mut end_branches = vec![];
                for i in 0..alternatives.len() {
                    let alt = &alternatives[i];

                    self.scope(&mut |this| {
                        let pattern_start = instructions.len() as isize;
                        let mut branches = vec![];
                        let i = this.stack_size - 1;
                        let stack_increase =
                            this.compile_pattern(&alt.pattern, &mut branches, instructions, i);
                        let pattern_end = instructions.len() as isize;
                        this.compile(&alt.expression, instructions, strict);
                        instructions.push(Slide(stack_increase));
                        instructions.push(Jump(0)); //Should jump to the end
                        end_branches.push(instructions.len() - 1);

                        //Here the current branch ends and the next one starts
                        //We need to set all the jump instructions to their actual location
                        //and append Slide instructions to bring the stack back to normal if the match fails
                        for j in ((pattern_start + 1)..(pattern_end + 1)).rev() {
                            match instructions[j as usize] {
                                Jump(_) => {
                                    instructions[j as usize] = Jump(instructions.len());
                                }
                                JumpFalse(_) => {
                                    instructions[j as usize] = JumpFalse(instructions.len())
                                }
                                Split(size) => instructions.push(Pop(size)),
                                _ => (),
                            }
                        }
                    });
                }
                for branch in end_branches.iter() {
                    instructions[*branch] = Jump(instructions.len());
                }
                //Remove the matched expr
                instructions.push(Slide(1));
                if strict {
                    instructions.push(Eval);
                }
            }
            &Lambda(_, _) => panic!("Error: Found non-lifted lambda when compiling expression"),
        }
    }
    fn compile_apply(
        &mut self,
        expr: &Expr<Id>,
        args: ArgList,
        instructions: &mut Vec<Instruction>,
        strict: bool,
    ) {
        //Unroll the applications until the function is found
        match *expr {
            Apply(ref func, ref arg) => {
                return self.compile_apply(
                    &**func,
                    ArgList::Cons(&**arg, &args),
                    instructions,
                    strict,
                )
            }
            _ => (),
        }
        //Tracks if the application is a regular function in which case we need to add Mkap instructions at the end
        let mut is_function = true;
        let arg_length;
        match *expr {
            Identifier(ref name) => {
                //When compiling a variable which has constraints a new instance dictionary
                //might be created which is returned here and added to the assembly
                let mut is_primitive = false;
                let var = self
                    .find(name.name)
                    .unwrap_or_else(|| panic!("Error: Undefined variable {:?}", *name));
                match var {
                    Var::Primitive(..) => is_primitive = true,
                    _ => (),
                }
                arg_length = self.compile_args(&args, instructions, is_primitive);
                match var {
                    Var::Stack(index) => {
                        instructions.push(Push(index));
                    }
                    Var::Global(index) => {
                        instructions.push(PushGlobal(index));
                    }
                    Var::Constructor(tag, arity) => {
                        instructions.push(Pack(tag, arity));
                        is_function = false;
                    }
                    Var::Builtin(index) => {
                        instructions.push(PushBuiltin(index));
                    }
                    Var::Class(typ, constraints, var) => {
                        debug!(
                            "Var::Class ({:?}, {:?}, {:?}) {:?}",
                            typ,
                            constraints,
                            var,
                            expr.get_type()
                        );
                        self.compile_instance_variable(
                            expr.get_type(),
                            instructions,
                            name.name,
                            typ,
                            constraints,
                            var,
                        );
                    }
                    Var::Constraint(index, bind_type, constraints) => {
                        debug!(
                            "Var::Constraint {:?} ({:?}, {:?}, {:?})",
                            name, index, bind_type, constraints
                        );
                        self.compile_with_constraints(
                            name.name,
                            expr.get_type(),
                            bind_type,
                            constraints,
                            instructions,
                        );
                        instructions.push(PushGlobal(index));
                        instructions.push(Mkap);
                    }
                    Var::Primitive(num_args, instruction) => {
                        if num_args == arg_length {
                            instructions.push(instruction);
                        } else {
                            panic!(
                                "Expected {:?} arguments for {:?}, got {:?}",
                                num_args, name, arg_length
                            )
                        }
                        is_function = false;
                    }
                    Var::Newtype => {
                        match args {
                            ArgList::Cons(_, _) => {
                                //Do nothing
                            }
                            ArgList::Nil => {
                                //translate into id application
                                let x = self.find(Name { name: intern("id"), uid: 0 })
                                    .expect("Compiler error: Prelude.id must be in scope for compilation of newtype");
                                match x {
                                    Var::Global(index) => {
                                        instructions.push(PushGlobal(index));
                                    }
                                    _ => panic!(),
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
        self.stack_size -= arg_length;
        if is_function {
            for _ in 0..arg_length {
                instructions.push(Mkap);
            }
            if strict {
                instructions.push(Eval);
            }
        }
    }

    fn compile_args(
        &mut self,
        args: &ArgList,
        instructions: &mut Vec<Instruction>,
        strict: bool,
    ) -> usize {
        match *args {
            ArgList::Cons(arg, rest) => {
                let i = self.compile_args(rest, instructions, strict);
                //The stack has increased by 1 until the function compiles and reduces it wtih Pack or Mkap
                self.compile(arg, instructions, strict);
                self.stack_size += 1;
                i + 1
            }
            ArgList::Nil => 0,
        }
    }

    ///Compile a function which is defined in a class
    fn compile_instance_variable(
        &mut self,
        actual_type: &Type<Name>,
        instructions: &mut Vec<Instruction>,
        name: Name,
        function_type: &Type<Name>,
        constraints: &[Constraint<Name>],
        var: &TypeVariable,
    ) {
        match try_find_instance_type(var, function_type, actual_type) {
            Some(typename) => {
                //We should be able to retrieve the instance directly
                let mut b = "#".to_string();
                b.push_str(typename);
                b.push_str(name.as_ref());
                let instance_fn_name = Name {
                    name: intern(b.as_ref()),
                    uid: name.uid,
                };
                match self.find(instance_fn_name) {
                    Some(Var::Global(index)) => {
                        instructions.push(PushGlobal(index));
                    }
                    Some(Var::Constraint(index, function_type, constraints)) => {
                        self.compile_with_constraints(
                            instance_fn_name,
                            actual_type,
                            function_type,
                            constraints,
                            instructions,
                        );
                        instructions.push(PushGlobal(index));
                        instructions.push(Mkap);
                    }
                    _ => panic!("Unregistered instance function {:?}", instance_fn_name),
                }
            }
            None => {
                self.compile_with_constraints(
                    name,
                    actual_type,
                    function_type,
                    constraints,
                    instructions,
                )
            }
        }
    }

    ///Compile the loading of a variable which has constraints and will thus need to load a dictionary with functions as well
    fn compile_with_constraints(
        &mut self,
        name: Name,
        actual_type: &Type<Name>,
        function_type: &Type<Name>,
        constraints: &[Constraint<Name>],
        instructions: &mut Vec<Instruction>,
    ) {
        match self.find(Name {
            name: intern("$dict"),
            uid: 0,
        }) {
            Some(Var::Stack(_)) => {
                //Push dictionary or member of dictionary
                match self.push_dictionary_member(constraints, name) {
                    Some(index) => instructions.push(PushDictionaryMember(index)),
                    None => {
                        let dictionary_key =
                            find_specialized_instances(function_type, actual_type, constraints);
                        self.push_dictionary(constraints, &*dictionary_key, instructions);
                    }
                }
            }
            _ => {
                //get dictionary index
                //push dictionary
                let dictionary_key =
                    find_specialized_instances(function_type, actual_type, constraints);
                self.push_dictionary(constraints, &*dictionary_key, instructions);
            }
        }
    }

    fn push_dictionary(
        &mut self,
        context: &[Constraint<Name>],
        constraints: &[(Name, Type<Name>)],
        instructions: &mut Vec<Instruction>,
    ) {
        debug!("Push dictionary {:?} ==> {:?}", context, constraints);
        for &(ref class, ref typ) in constraints.iter() {
            self.fold_dictionary(*class, typ, instructions);
            instructions.push(ConstructDictionary(constraints.len()));
        }
    }

    //Writes instructions which pushes a dictionary for the type to the top of the stack
    fn fold_dictionary(
        &mut self,
        class: Name,
        typ: &Type<Name>,
        instructions: &mut Vec<Instruction>,
    ) {
        match *typ {
            Type::Constructor(ref ctor) => {
                //Simple
                debug!("Simple for {:?}", ctor);
                //Push static dictionary to the top of the stack
                let index = self.find_dictionary_index(&[(class.clone(), typ.clone())]);
                instructions.push(PushDictionary(index));
            }
            Type::Application(ref lhs, ref rhs) => {
                debug!("App for ({:?} {:?})", lhs, rhs);
                //For function in functions
                // Mkap function fold_dictionary(rhs)
                self.fold_dictionary(class, &**lhs, instructions);
                self.fold_dictionary(class, &**rhs, instructions);
                instructions.push(MkapDictionary);
            }
            Type::Variable(ref var) => {
                //This variable must appear in the context
                let mut has_constraint = false;
                let mut index = 0;
                for constraint in self.context.iter() {
                    if constraint.variables[0] == *var && constraint.class == class {
                        has_constraint = true;
                        break;
                    }
                    let (_, _, decls) = self.find_class(constraint.class).unwrap();
                    index += decls.len();
                }
                if has_constraint {
                    //Found the variable in the constraints
                    let num_class_functions = self
                        .find_class(class)
                        .map(|(_, _, decls)| decls.len())
                        .unwrap();
                    debug!(
                        "Use previous dict for {:?} at {:?}..{:?}",
                        var, index, num_class_functions
                    );
                    instructions.push(PushDictionaryRange(index, num_class_functions));
                } else {
                    debug!("No dict for {:?}", var);
                }
            }
            _ => panic!("Did not expect generic"),
        }
    }

    ///Lookup which index in the instance dictionary that holds the function called 'name'
    fn push_dictionary_member(
        &self,
        constraints: &[Constraint<Name>],
        name: Name,
    ) -> Option<usize> {
        if constraints.len() == 0 {
            panic!(
                "Attempted to push dictionary member '{:?}' with no constraints",
                name
            )
        }
        let mut ii = 0;
        for c in constraints.iter() {
            let result =
                self.walk_classes(c.class, &mut |declarations| -> Option<usize> {
                    for decl in declarations.iter() {
                        if decl.name == name {
                            return Some(ii);
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
    fn walk_classes<T>(
        &self,
        class: Name,
        f: &mut dyn FnMut(&[TypeDeclaration<Name>]) -> Option<T>,
    ) -> Option<T> {
        let (constraints, _, declarations) = self
            .find_class(class)
            .expect("Compiler error: Expected class");
        //Look through the functions in any super classes first
        constraints
            .iter()
            .filter_map(|constraint| self.walk_classes(constraint.class, f))
            .next()
            .or_else(|| (*f)(declarations))
    }

    ///Find the index of the instance dictionary for the constraints and types in 'constraints'
    ///Returns the index
    fn find_dictionary_index(&mut self, constraints: &[(Name, Type<Name>)]) -> usize {
        //Check if the dictionary already exist
        let dict_len = self.instance_dictionaries.len();
        for ii in 0..dict_len {
            if self.instance_dictionaries[ii].0 == constraints {
                return ii;
            }
        }

        if constraints.len() == 0 {
            panic!("Error: Attempted to compile dictionary with no constraints at <unknown>");
        }
        let mut function_indexes = vec![];
        self.add_class(constraints, &mut function_indexes);
        self.instance_dictionaries
            .push((constraints.to_owned(), function_indexes));
        dict_len
    }

    fn add_class(&self, constraints: &[(Name, Type<Name>)], function_indexes: &mut Vec<usize>) {
        for &(ref class_name, ref typ) in constraints.iter() {
            self.walk_classes(*class_name, &mut |declarations| -> Option<()> {
                for decl in declarations.iter() {
                    let x = match extract_applied_type(typ) {
                        &Type::Constructor(ref x) => x,
                        _ => panic!("{:?}", typ),
                    };
                    let mut b = "#".to_string();
                    b.push_str(x.name.as_ref());
                    b.push_str(decl.name.as_ref());
                    let f = intern(b.as_ref());
                    let name = Name {
                        name: f,
                        uid: decl.name.uid,
                    };
                    match self.find(name) {
                        Some(Var::Global(index)) => {
                            function_indexes.push(index as usize);
                        }
                        Some(Var::Constraint(index, _, _)) => {
                            function_indexes.push(index as usize); //TODO this is not really correct since this function requires a dictionary
                        }
                        var => panic!("Did not find function {:?} {:?}", name, var),
                    }
                }
                None
            });
        }
    }

    ///Compiles a pattern.
    ///An index to the Jump instruction which is taken when the match fails is stored in the branches vector
    ///These instructions will need to be updated later with the correct jump location.
    fn compile_pattern(
        &mut self,
        pattern: &Pattern<Id>,
        branches: &mut Vec<usize>,
        instructions: &mut Vec<Instruction>,
        stack_size: usize,
    ) -> usize {
        debug!("Pattern {:?} at {:?}", pattern, stack_size);
        match pattern {
            &Pattern::Constructor(ref name, ref patterns) => {
                instructions.push(Push(stack_size));
                match self.find_constructor(name.name) {
                    Some((tag, _)) => {
                        instructions.push(CaseJump(tag as usize));
                        branches.push(instructions.len());
                        instructions.push(Jump(0));
                    }
                    _ => panic!("Undefined constructor {:?}", *name),
                }
                instructions.push(Split(patterns.len()));
                self.stack_size += patterns.len();
                for (i, p) in patterns.iter().enumerate() {
                    let index = self.stack_size - patterns.len() + i;
                    self.new_var_at(p.name.clone(), index);
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
            &Pattern::WildCard => 0,
        }
    }
}

///Attempts to find the actual type of the for the variable which has a constraint
fn try_find_instance_type<'a>(
    class_var: &TypeVariable,
    class_type: &Type<Name>,
    actual_type: &'a Type<Name>,
) -> Option<&'a str> {
    match (class_type, actual_type) {
        (&Type::Variable(ref var), _) if var == class_var => {
            //Found the class variable so return the name of the type
            match extract_applied_type(actual_type) {
                &Type::Constructor(ref op) => Some(op.name.as_ref()),
                _ => None,
            }
        }
        (&Type::Constructor(ref class_op), &Type::Constructor(ref actual_op)) => {
            assert_eq!(class_op.name, actual_op.name);
            None
        }
        (&Type::Application(ref lhs1, ref rhs1), &Type::Application(ref lhs2, ref rhs2)) => {
            try_find_instance_type(class_var, &**lhs1, &**lhs2)
                .or_else(|| try_find_instance_type(class_var, &**rhs1, &**rhs2))
        }
        _ => None,
    }
}

#[allow(dead_code)]
pub fn compile(contents: &str) -> Result<Assembly, ::std::string::String> {
    let mut type_env = TypeEnvironment::new();
    compile_with_type_env(&mut type_env, &[], contents)
}
#[allow(dead_code)]
pub fn compile_with_type_env<'a>(
    type_env: &mut TypeEnvironment<'a>,
    assemblies: &[&'a Assembly],
    contents: &str,
) -> Result<Assembly, ::std::string::String> {
    use crate::parser::Parser;

    let mut parser = Parser::new(contents.chars());
    let module = parser.module().map_err(|e| format!("{:?}", e))?;
    let mut module = rename_module(module).map_err(|e| format!("{}", e))?;
    for assem in assemblies.iter() {
        type_env.add_types(*assem);
    }
    type_env
        .typecheck_module(&mut module)
        .map_err(|e| format!("{}", e))?;
    let core_module = do_lambda_lift(translate_module(module));
    let mut compiler = Compiler::new();
    for assem in assemblies.iter() {
        compiler.assemblies.push(*assem);
    }
    Ok(compiler.compile_module(&core_module))
}

pub fn compile_string(module: &str) -> Result<Vec<Assembly>, ::std::string::String> {
    use crate::typecheck::typecheck_string;
    let modules = typecheck_string(module)?;
    compile_module_(modules)
}

///Takes a module name and does everything needed up to and including compiling the module
///and its imported modules
pub fn compile_module(module: &str) -> Result<Vec<Assembly>, ::std::string::String> {
    use crate::typecheck::typecheck_module;
    let modules = typecheck_module(module)?;
    compile_module_(modules)
}

fn compile_module_(
    modules: Vec<crate::module::Module<Name>>,
) -> Result<Vec<Assembly>, ::std::string::String> {
    let core_modules: Vec<Module<Id<Name>>> = translate_modules(modules)
        .into_iter()
        .map(|module| do_lambda_lift(module))
        .collect();
    let mut assemblies = vec![];
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

    use {
        crate::{
            compiler::{
                compile_with_type_env,
                Assembly,
                Compiler,
                Instruction::*,
            },
            interner::*,
            typecheck::TypeEnvironment,
        },
        std::{
            fs::File,
            io::Read,
            path::Path,
        },
        test::Bencher,
    };

    fn compile(contents: &str) -> Assembly {
        super::compile(contents).unwrap()
    }

    #[test]
    fn add() {
        let file = "main = primIntAdd 1 2";
        let assembly = compile(file);

        assert_eq!(
            assembly.super_combinators[0].instructions,
            vec![PushInt(2), PushInt(1), Add, Update(0), Unwind]
        );
    }

    #[test]
    fn add_double() {
        let file = r"add x y = primDoubleAdd x y
main = add 2. 3.";
        let assembly = compile(file);

        assert_eq!(
            assembly.super_combinators[0].instructions,
            vec![
                Push(1),
                Eval,
                Push(0),
                Eval,
                DoubleAdd,
                Update(0),
                Pop(2),
                Unwind
            ]
        );
        assert_eq!(
            assembly.super_combinators[1].instructions,
            vec![
                PushFloat(3.),
                PushFloat(2.),
                PushGlobal(0),
                Mkap,
                Mkap,
                Eval,
                Update(0),
                Unwind
            ]
        );
    }
    #[test]
    fn push_num_double() {
        let file = r"main = primDoubleAdd 2 3";
        let assembly = compile(file);

        assert_eq!(
            assembly.super_combinators[0].instructions,
            vec![PushFloat(3.), PushFloat(2.), DoubleAdd, Update(0), Unwind]
        );
    }

    #[test]
    fn application() {
        let file = r"add x y = primIntAdd x y
main = add 2 3";
        let assembly = compile(file);

        assert_eq!(
            assembly.super_combinators[1].instructions,
            vec![
                PushInt(3),
                PushInt(2),
                PushGlobal(0),
                Mkap,
                Mkap,
                Eval,
                Update(0),
                Unwind
            ]
        );
    }

    #[test]
    fn compile_constructor() {
        let file = r"main = primIntAdd 1 0 : []";
        let assembly = compile(file);

        assert_eq!(
            assembly.super_combinators[0].instructions,
            vec![
                Pack(0, 0),
                PushInt(0),
                PushInt(1),
                Add,
                Pack(1, 2),
                Update(0),
                Unwind
            ]
        );
    }

    #[test]
    fn compile_tuple() {
        let file = r"test x y = (primIntAdd 0 1, x, y)";
        let assembly = compile(file);

        assert_eq!(
            assembly.super_combinators[0].instructions,
            vec![
                Push(1),
                Push(0),
                PushInt(1),
                PushInt(0),
                Add,
                Pack(0, 3),
                Update(0),
                Pop(2),
                Unwind
            ]
        );
    }

    #[test]
    fn compile_case() {
        let file = r"main = case [primIntAdd 1 0] of
    x:xs -> x
    [] -> 2";
        let assembly = compile(file);

        assert_eq!(
            assembly.super_combinators[0].instructions,
            vec![
                Pack(0, 0),
                PushInt(0),
                PushInt(1),
                Add,
                Pack(1, 2),
                Push(0),
                CaseJump(1),
                Jump(14),
                Split(2),
                Push(1),
                Eval,
                Slide(2),
                Jump(22),
                Pop(2),
                Push(0),
                CaseJump(0),
                Jump(22),
                Split(0),
                PushInt(2),
                Slide(0),
                Jump(22),
                Pop(0),
                Slide(1),
                Eval,
                Update(0),
                Unwind
            ]
        );
    }

    #[test]
    fn compile_class_constraints() {
        let file = r"class Test a where
    test :: a -> Int

instance Test Int where
    test x = x

main = test (primIntAdd 6 0)";
        let assembly = compile(file);

        let main = &assembly.super_combinators[0];
        assert_eq!(main.name.name, intern("main"));
        assert_eq!(
            main.instructions,
            vec![
                PushInt(0),
                PushInt(6),
                Add,
                PushGlobal(1),
                Mkap,
                Eval,
                Update(0),
                Unwind
            ]
        );
    }

    #[test]
    fn compile_class_constraints_unknown() {
        let file = r"class Test a where
    test :: a -> Int

instance Test Int where
    test x = x

main x = primIntAdd (test x) 6";
        let assembly = compile(file);

        let main = &assembly.super_combinators[0];
        assert_eq!(main.name.name, intern("main"));
        assert_eq!(
            main.instructions,
            vec![
                PushInt(6),
                Push(1),
                PushDictionaryMember(0),
                Mkap,
                Eval,
                Add,
                Update(0),
                Pop(2),
                Unwind
            ]
        );
    }

    #[test]
    fn compile_prelude() {
        let prelude;
        let mut type_env = TypeEnvironment::new();
        let mut contents = ::std::string::String::new();
        File::open("Prelude.hs")
            .and_then(|mut f| f.read_to_string(&mut contents))
            .unwrap();
        prelude = compile_with_type_env(&mut type_env, &[], &contents).unwrap();

        let assembly =
            compile_with_type_env(&mut type_env, &[&prelude], r"main = id (primIntAdd 2 0)")
                .unwrap();

        let sc = &assembly.super_combinators[0];
        let id_index = prelude
            .super_combinators
            .iter()
            .position(|sc| sc.name.name == intern("id"))
            .unwrap();
        assert_eq!(
            sc.instructions,
            vec![
                PushInt(0),
                PushInt(2),
                Add,
                PushGlobal(id_index),
                Mkap,
                Eval,
                Update(0),
                Unwind
            ]
        );
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
",
        );
    }

    #[test]
    fn binding_pattern() {
        compile(
            r"
test f (x:xs) = f x : test f xs
test _ [] = []
",
        );
    }

    #[test]
    fn newtype() {
        //Test that the newtype constructor is newer constucted
        let file = r"
newtype Test a = Test [a]
test = Test [1::Int]";
        let assembly = compile(file);

        let test = &assembly.super_combinators[0];
        assert_eq!(
            test.instructions,
            vec![Pack(0, 0), PushInt(1), Pack(1, 2), Update(0), Unwind]
        );
    }

    #[bench]
    fn bench_prelude(b: &mut Bencher) {
        use crate::{
            core::translate::translate_module,
            lambda_lift::do_lambda_lift,
            parser::Parser,
            renamer::tests::rename_module,
        };

        let path = &Path::new("Prelude.hs");
        let mut contents = ::std::string::String::new();
        File::open(path)
            .and_then(|mut f| f.read_to_string(&mut contents))
            .unwrap();
        let mut parser = Parser::new(contents.chars());
        let mut module = rename_module(parser.module().unwrap());
        let mut type_env = TypeEnvironment::new();
        type_env.typecheck_module_(&mut module);
        let core_module = do_lambda_lift(translate_module(module));
        b.iter(|| {
            let mut compiler = Compiler::new();
            compiler.compile_module(&core_module)
        });
    }
}
