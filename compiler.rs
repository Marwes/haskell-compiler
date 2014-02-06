use module::*;
use Scope;
use typecheck::{Types, TypeEnvironment, function_type};

#[deriving(Eq)]
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
    PushDictionary(uint),
    PushDictionaryMember(uint),
}

#[deriving(Clone)]
enum Var<'a> {
    StackVariable(uint),
    GlobalVariable(uint),
    ConstructorVariable(u16, u16),
    ClassVariable(&'a Type, TypeVariable),
    ConstraintVariable(uint, &'a Type, &'a[TypeOperator])
}

pub struct SuperCombinator {
    arity : uint,
    name: ~str,
    assembly_id: uint,
    instructions : ~[Instruction],
    type_declaration: TypeDeclaration,
    constraints: ~[TypeOperator]
}
impl SuperCombinator {
    fn new() -> SuperCombinator {
        SuperCombinator { arity : 0, name: ~"", instructions : ~[], type_declaration: Default::default(), constraints: ~[], assembly_id: 0 }
    }
}

pub struct Assembly {
    superCombinators: ~[SuperCombinator],
    instance_dictionaries: ~[~[uint]],
    classes: ~[Class],
    instances: ~[TypeOperator],
    data_definitions: ~[DataDefinition],
    offset: uint
}

trait Globals {
    ///Lookup a global variable
    fn find_global<'a>(&'a self, name: &str) -> Option<Var<'a>>;
}

impl Globals for Assembly {
    fn find_global<'a>(&'a self, name: &str) -> Option<Var<'a>> {
        let mut index = 0;
        for sc in self.superCombinators.iter() {
            if name == sc.name {
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
                if decl.name.equiv(&name) {
                    return Some(ClassVariable(&decl.typ, class.variable));
                }
            }
        }
        
        for data_def in self.data_definitions.iter() {
            for ctor in data_def.constructors.iter() {
                if name == ctor.name {
                    return Some(ConstructorVariable(ctor.tag as u16, ctor.arity as u16));
                }
            }
        }
        return None;
    }
}

fn find_global<'a>(module: &'a Module, offset: uint, name: &str) -> Option<Var<'a>> {
    
    for dataDef in module.dataDefinitions.iter() {
        for ctor in dataDef.constructors.iter() {
            if ctor.name.equiv(&name) {
                return Some(ConstructorVariable(ctor.tag as u16, ctor.arity as u16));
            }
        }
    }
    
    for class in module.classes.iter() {
        for decl in class.declarations.iter() {
            if decl.name.equiv(&name) {
                return Some(ClassVariable(&decl.typ, class.variable));
            }
        }
    }

    let mut global_index = 0;
    for instance in module.instances.iter() {
        for bind in instance.bindings.iter() {
            if bind.name.equiv(&name) {
                return Some(GlobalVariable(offset + global_index));
            }
            global_index += 1;
        }
    }
    for bind in module.bindings.iter() {
        if bind.name.equiv(&name) {
            let typ = &bind.expression.typ;
            let constraints = &bind.typeDecl.context;
            if constraints.len() > 0 {
                return Some(ConstraintVariable(offset + global_index, typ, *constraints));
            }
            else {
                return Some(GlobalVariable(offset + global_index));
            }
        }
        global_index += 1;
    }
    None
}

impl Types for Assembly {
    ///Lookup a type
    fn find_type<'a>(&'a self, name: &str) -> Option<&'a Type> {
        for sc in self.superCombinators.iter() {
            if sc.name.equiv(&name) {
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
    fn has_instance(&self, classname: &str, typ: &TypeOperator) -> bool {
        for op in self.instances.iter() {
            if classname == op.name && op.types[0].op() == typ {
                return true;
            }
        }
        false
    }
    fn each_typedeclaration(&self, func: |&TypeDeclaration|) {
        for sc in self.superCombinators.iter() {
            func(&sc.type_declaration);
        }
        
        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                func(decl);
            }
        }
    }
}

pub struct Compiler<'a> {
    type_env: &'a TypeEnvironment<'a>,
    ///Hashmap containging class names mapped to the functions it contains
    instance_dictionaries: ~[(~[TypeOperator], ~[uint])],
    stackSize : uint,
    ///Array of all the assemblies which can be used to lookup functions in
    assemblies: ~[&'a Assembly],
}


impl <'a> Compiler<'a> {
    pub fn new(type_env: &'a TypeEnvironment) -> Compiler<'a> {
        Compiler { type_env: type_env, instance_dictionaries: ~[],
            stackSize : 0, assemblies: ~[] }
    }
    
    pub fn compileModule(&mut self, module : &Module) -> Assembly {

        let mut assembly = Assembly {
            superCombinators: ~[],
            instance_dictionaries: ~[],
            offset: self.assemblies.iter().flat_map(|assembly| assembly.superCombinators.iter()).len(),
            classes: module.classes.clone(),
            instances: module.instances.iter().map(
                |inst| TypeOperator { name: inst.classname.clone(), types: ~[TypeOperator(inst.typ.clone())] }).collect(),
            data_definitions: ~[]
        };
        
        for def in module.dataDefinitions.iter() {
            let mut constructors = ~[];
            for ctor in def.constructors.iter() {
                constructors.push(ctor.clone());
            }
            assembly.data_definitions.push(def.clone());
        }

        for class in module.classes.iter() {
            let mut function_names = ~[];
            for decl in class.declarations.iter() {
                function_names.push(decl.name.clone());
            }
        }
        
        //Compile all bindings
        for instance in module.instances.iter() {
            for bind in instance.bindings.iter() {
                let mut sc = self.compileBinding(bind, Some(module));
                sc.name = bind.name.clone();
                sc.assembly_id = self.assemblies.len();
                assembly.superCombinators.push(sc);
            }
        }
        for bind in module.bindings.iter() {
            let mut sc = self.compileBinding(bind, Some(module));
            let constraints = self.type_env.find_constraints(&bind.expression.typ);
            sc.constraints = constraints;
            sc.name = bind.name.clone();
            assembly.superCombinators.push(sc);
        }

        for &(_, ref dict) in self.instance_dictionaries.iter() {
            assembly.instance_dictionaries.push(dict.clone());
        }
        assembly
    }
    fn compileBinding(&mut self, bind : &Binding, module: Option<&Module>) -> SuperCombinator {
        debug!("Compiling binding {}", bind.name);
        let mut comb = SuperCombinator::new();
        comb.type_declaration = bind.typeDecl.clone();
        let dict_arg = if self.type_env.find_constraints(&comb.type_declaration.typ).len() > 0 { 1 } else { 0 };
        comb.arity = bind.arity + dict_arg;
        let mut stack = CompilerNode { compiler: self, stack: Scope::new(), constraints: bind.typeDecl.context, module: module };
        if dict_arg == 1 {
            stack.newStackVar(~"$dict");
        }
        match &bind.expression.expr {
            &Lambda(_, _) => {
                stack.compile(&bind.expression, &mut comb.instructions, true);
                comb.instructions.push(Update(0));
                comb.instructions.push(Pop(comb.arity));
                comb.instructions.push(Unwind);
            }
            _ => {
                stack.compile(&bind.expression, &mut comb.instructions, true);
                comb.instructions.push(Update(0));
                comb.instructions.push(Unwind);
            }
       }
       comb
    }
    pub fn compileExpression(&mut self, expr: &TypedExpr) -> ~[Instruction] {
        let mut stack = CompilerNode { compiler: self, stack: Scope::new(), constraints: [], module: None };
        let mut instructions = ~[];
        stack.compile(expr, &mut instructions, false);
        instructions
    }

}

struct CompilerNode<'a, 'b, 'c> {
    stack: Scope<'a, Var<'a>>,
    compiler: &'a mut Compiler<'b>,
    constraints: &'a [TypeOperator],
    module: Option<&'c Module>
}

//CompilerNode are only used locally and the destructor are just to reduce the stack size
//so this should be safe(?)
#[unsafe_destructor]
impl <'a, 'b, 'c> Drop for CompilerNode<'a, 'b, 'c> {
    fn drop(&mut self) {
        self.compiler.stackSize -= self.stack.variables.len();
    }
}

impl <'a, 'b, 'c> CompilerNode<'a, 'b, 'c> {
    
    ///Find a variable by walking through the stack followed by all globals
    fn find(&'a self, identifier : &str) -> Option<Var<'a>> {
        self.stack.find(identifier).map(|x| x.clone())
        .or_else(|| {
            match self.module {
                Some(ref module) => {
                    let n = self.compiler.assemblies.len();
                    let offset = if n > 0 {
                        let assembly = self.compiler.assemblies[n-1];
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
            for assembly in self.compiler.assemblies.iter() {
                match assembly.find_global(identifier) {
                    Some(var) => return Some(var),
                    None => ()
                }
            }
            None
        }).or_else(|| {
            match identifier {
                &"[]" => Some(ConstructorVariable(0, 0)),
                &":" => Some(ConstructorVariable(1, 2)),
                _ => None
            }
        })
    }

    fn find_class<'r>(&'r self, name: &str) -> Option<&'r Class> {
        self.module.and_then(|m| m.find_class(name))
            .or_else(|| {
            for types in self.compiler.assemblies.iter() {
                match types.find_class(name) {
                    Some(result) => return Some(result),
                    None => ()
                }
            }
            None
        })
    }

    fn newStackVar(&mut self, identifier : ~str) {
        self.stack.insert(identifier, StackVariable(self.compiler.stackSize));
        self.compiler.stackSize += 1;
    }
    fn removeStackVar(&mut self, identifier : &~str) {
        self.stack.variables.remove(identifier);
        self.compiler.stackSize -= 1;
    }

    ///Create a new scope for variables, such as a lambda or let bindings
    fn child(&'a self) -> CompilerNode<'a, 'b, 'c> {
        CompilerNode { compiler: self.compiler, stack : self.stack.child(), constraints: self.constraints, module: self.module }
    }

    ///Compile an expression by appending instructions to the instructions array
    fn compile(&mut self, expr : &TypedExpr, instructions : &mut ~[Instruction], strict: bool) {
        debug!("Compiling {}", expr.expr);
        match &expr.expr {
            &Identifier(ref name) => {
                //When compiling a variable which has constraints a new instance dictionary
                //might be created which is returned here and added to the assembly
                let maybe_new_dict = match self.find(*name) {
                    None => fail!("Undefined variable " + *name),
                    Some(var) => {
                        match var {
                            StackVariable(index) => { instructions.push(Push(index)); None }
                            GlobalVariable(index) => { instructions.push(PushGlobal(index)); None }
                            ConstructorVariable(tag, arity) => { instructions.push(Pack(tag, arity)); None }
                            ClassVariable(typ, var) => self.compile_instance_variable(&expr.typ, instructions, *name, typ, &var),
                            ConstraintVariable(index, _, constraints) => {
                                let x = self.compile_with_constraints(*name, &expr.typ, constraints, instructions);
                                instructions.push(PushGlobal(index));
                                instructions.push(Mkap);
                                x
                            }
                        }
                    }
                };
                match maybe_new_dict {
                    Some(dict) => self.compiler.instance_dictionaries.push(dict),
                    None => ()
                }
                if strict {
                    instructions.push(Eval);
                }
            }
            &Number(num) => {
                if expr.typ == Type::new_op(~"Int", ~[]) {
                    instructions.push(PushInt(num));
                }
                else if expr.typ == Type::new_op(~"Double", ~[]) {
                    instructions.push(PushFloat(num as f64));
                }
                else {
                    let mut fromInteger = TypedExpr::new(Identifier(~"fromInteger"));
                    fromInteger.typ = function_type(&Type::new_op(~"Int", ~[]), &expr.typ);
                    let mut number = TypedExpr::new(Number(num));
                    number.typ = Type::new_op(~"Int", ~[]);
                    let mut apply = TypedExpr::new(Apply(~fromInteger, ~number));
                    apply.typ = expr.typ.clone();
                    self.compile(&apply, instructions, strict);
                }

            }
            &Rational(num) => {
                if expr.typ == Type::new_op(~"Double", ~[]) {
                    instructions.push(PushFloat(num));
                }
                else {
                    let mut fromRational = TypedExpr::new(Identifier(~"fromRational"));
                    fromRational.typ = function_type(&Type::new_op(~"Double", ~[]), &expr.typ);
                    let mut number = TypedExpr::new(Rational(num));
                    number.typ = Type::new_op(~"Double", ~[]);
                    let mut apply = TypedExpr::new(Apply(~fromRational, ~number));
                    apply.typ = expr.typ.clone();
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
            &Apply(ref func, ref arg) => {
                if !self.primitive(*func, *arg, instructions) {
                    self.compile(*arg, instructions, false);
                    self.compile(*func, instructions, false);
                    match &instructions[instructions.len() - 1] {
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
                self.newStackVar(varname.clone());
                self.compile(*body, instructions, false);
            }
            &Let(ref bindings, ref body) => {
                for bind in bindings.iter() {
                    self.newStackVar(bind.name.clone());
                    self.compile(&bind.expression, instructions, false);
                }
                self.compile(*body, instructions, strict);
                instructions.push(Slide(bindings.len()));
            }
            &Case(ref body, ref alternatives) => {
                self.compile(*body, instructions, true);
                self.newStackVar(~"");//Dummy variable for the case expression
                let mut branches = ~[];
                for alt in alternatives.iter() {
                    self.compile_pattern(&alt.pattern, &mut branches, instructions);
                }
                self.removeStackVar(&~"");
                for i in range(0, alternatives.len()) {
                    let alt = &alternatives[i];
                    
                    //Set the jump instruction to jump to this place
                    instructions[branches[i]] = Jump(instructions.len());
                    
                    let mut childScope = self.child();
                    let num_vars = childScope.add_pattern_variables(&alt.pattern, instructions);
                    childScope.compile(&alt.expression, instructions, strict);
                    instructions.push(Slide(num_vars));
                    
                    //Reuse branches for the next Jump
                    branches[i] = instructions.len();
                    instructions.push(Jump(0));
                }
                for branch in branches.iter() {
                    instructions[*branch] = Jump(instructions.len());
                }
                if strict {
                    instructions.push(Eval);
                }
            }
        }
    }

    ///Compile a function which is defined in a class
    fn compile_instance_variable(&self, actual_type: &Type, instructions: &mut ~[Instruction], name: &str, typ: &Type, var: &TypeVariable) -> Option<(~[TypeOperator], ~[uint])> {
        match try_find_instance_type(var, typ, actual_type) {
            Some(typename) => {
                //We should be able to retrieve the instance directly
                let instance_fn_name = "#" + typename + name;
                match self.find(instance_fn_name) {
                    Some(GlobalVariable(index)) => {
                        instructions.push(PushGlobal(index));
                    }
                    _ => fail!("Unregistered instance function {}", instance_fn_name)
                }
                None
            }
            None => {
                let constraints = self.compiler.type_env.find_constraints(actual_type);
                self.compile_with_constraints(name, typ, constraints, instructions)
            }
        }
    }

    ///Compile the loading of a variable which has constraints and will thus need to load a dictionary with functions as well
    fn compile_with_constraints(&self, name: &str, typ: &Type, constraints: &[TypeOperator], instructions: &mut ~[Instruction]) -> Option<(~[TypeOperator], ~[uint])> {
        match self.find("$dict") {
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
                let dictionary_key = self.compiler.type_env.find_specialized_instances(name, typ);
                let (index, dict) = self.find_dictionary_index(dictionary_key);
                instructions.push(PushDictionary(index));
                dict
            }
        }
    }

    ///Lookup which index in the instance dictionary that holds the function called 'name'
    fn push_dictionary_member(&self, constraints: &[TypeOperator], name: &str) -> Option<uint> {
        if constraints.len() == 0 {
            fail!("Attempted to push dictionary member '{}' with no constraints", name)
        }
        for c in constraints.iter() {
            match self.find_class(c.name) {
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
    fn find_dictionary_index(&self, constraints: &[TypeOperator]) -> (uint, Option<(~[TypeOperator], ~[uint])>) {
        let dict_len = self.compiler.instance_dictionaries.len();
        for ii in range(0, dict_len) {
            if self.compiler.instance_dictionaries[ii].n0_ref().equiv(&constraints) {
                return (ii, None);
            }
        }

        if constraints.len() == 0 {
            fail!("Attempted to compile dictionary with no constraints");
        }
        let mut function_indexes = ~[];
        for c in constraints.iter() {
            match self.find_class(c.name) {
                Some(class) => {
                    assert!(class.declarations.len() > 0);
                    for decl in class.declarations.iter() {
                        let f = match &c.types[0] { 
                            &TypeOperator(ref op) => "#" + op.name + decl.name,
                            _ => fail!("Expected operator")
                        };
                        match self.find(f) {
                            Some(GlobalVariable(index)) => {
                                function_indexes.push(index as uint);
                            }
                            _ => fail!("Did not find function {}", f)
                        }
                    }
                }
                None => fail!("Could not find instance for {}", *c)
            }
        }
        (dict_len, Some((constraints.to_owned(), function_indexes)))
    }

    ///Attempt to compile a binary primitive, returning true if it succeded
    fn primitive(&mut self, func: &TypedExpr, arg: &TypedExpr, instructions: &mut ~[Instruction]) -> bool {
        match &func.expr {
            &Apply(ref prim_func, ref arg2) => {
                match &prim_func.expr {
                    &Identifier(ref name) => {
                        //Binary functions
                        let maybeOP = match *name {
                            ~"primIntAdd" => Some(Add),
                            ~"primIntSubtract" => Some(Sub),
                            ~"primIntMultiply" => Some(Multiply),
                            ~"primIntDivide" => Some(Divide),
                            ~"primIntRemainder" => Some(Remainder),
                            ~"primIntEQ" => Some(IntEQ),
                            ~"primIntLT" => Some(IntLT),
                            ~"primIntLE" => Some(IntLE),
                            ~"primIntGT" => Some(IntGT),
                            ~"primIntGE" => Some(IntGE),
                            ~"primDoubleAdd" => Some(DoubleAdd),
                            ~"primDoubleSubtract" => Some(DoubleSub),
                            ~"primDoubleMultiply" => Some(DoubleMultiply),
                            ~"primDoubleDivide" => Some(DoubleDivide),
                            ~"primDoubleRemainder" => Some(DoubleRemainder),
                            ~"primDoubleEQ" => Some(DoubleEQ),
                            ~"primDoubleLT" => Some(DoubleLT),
                            ~"primDoubleLE" => Some(DoubleLE),
                            ~"primDoubleGT" => Some(DoubleGT),
                            ~"primDoubleGE" => Some(DoubleGE),
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
                let n: &str = *name;
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

    fn compile_pattern(&self, pattern: &Pattern, branches: &mut ~[uint], instructions: &mut ~[Instruction]) {
        //TODO this is unlikely to work with nested patterns currently
        match pattern {
            &ConstructorPattern(ref name, ref patterns) => {
                match self.find(*name) {
                    Some(ConstructorVariable(tag, _)) => {
                        instructions.push(CaseJump(tag as uint));
                        branches.push(instructions.len());
                        instructions.push(Jump(0));//To be determined later
                    }
                    _ => fail!("Undefined constructor {}", *name)
                }
                for p in patterns.iter() {
                    self.compile_pattern(p, branches, instructions);
                }
            }
            _ => ()
        }
    }

    ///Add the variables of a pattern, returning how many variables that were added in total
    fn add_pattern_variables(&mut self, pattern: &Pattern, instructions: &mut ~[Instruction]) -> uint {
        match pattern {
            &ConstructorPattern(_, ref patterns) => {
                instructions.push(Split(patterns.len()));
                let mut vars = 0;
                for p in patterns.iter() {
                    vars += self.add_pattern_variables(p, instructions);
                }
                vars
            }
            &IdentifierPattern(ref ident) => {
                self.newStackVar(ident.clone());
                1
            }
            &NumberPattern(_) => 0
        }
    }
}

///Attempts to find the actual type of the for the variable which has a constraint
fn try_find_instance_type<'a>(class_var: &TypeVariable, class_type: &Type, actual_type: &'a Type) -> Option<&'a str> {
    match (class_type, actual_type) {
        (&TypeVariable(ref var), &TypeOperator(ref actual_op)) => {
            if var == class_var {
                //Found the class variable so return the name of the type
                let x : &str = actual_op.name;
                return Some(x)
            }
            None
        }
        (&TypeOperator(ref class_op), &TypeOperator(ref actual_op)) => {
            assert_eq!(class_op.name, actual_op.name);
            assert_eq!(class_op.types.len(), class_op.types.len());
            for ii in range(0, class_op.types.len()) {
                let result = try_find_instance_type(class_var, &class_op.types[ii], &actual_op.types[ii]);
                if result != None {
                    return result;
                }
            }
            None
        }
        _ => None
    }
}

#[cfg(test)]
mod tests {

use compiler::*;
use typecheck::TypeEnvironment;
use parser::Parser;
use typecheck::{identifier, apply, number};
use std::io::File;
use std::str::from_utf8;

#[test]
fn add() {
    let mut e = apply(apply(identifier(~"primIntAdd"), number(1)), number(2));
    let mut type_env = TypeEnvironment::new();
    type_env.typecheck(&mut e);
    let mut comp = Compiler::new(&type_env);
    let instr = comp.compileExpression(&e);

    assert_eq!(instr, ~[PushInt(2), PushInt(1), Add]);
}

#[test]
fn add_double() {
    let file =
r"add x y = primDoubleAdd x y
main = add 2. 3.";
    let mut parser = Parser::new(file.chars());
    let mut module = parser.module();
    let mut type_env = TypeEnvironment::new();
    type_env.typecheck_module(&mut module);
    let mut comp = Compiler::new(&type_env);
    let assembly = comp.compileModule(&module);

    assert_eq!(assembly.superCombinators[0].instructions, ~[Push(1), Eval, Push(0), Eval, DoubleAdd, Update(0), Pop(2), Unwind]);
    assert_eq!(assembly.superCombinators[1].instructions, ~[PushFloat(3.), PushFloat(2.), PushGlobal(0), Mkap, Mkap, Eval, Update(0), Unwind]);
}
#[test]
fn push_num_double() {
    let file =
r"main = primDoubleAdd 2 3";
    let mut parser = Parser::new(file.chars());
    let mut module = parser.module();
    let mut type_env = TypeEnvironment::new();
    type_env.typecheck_module(&mut module);
    let mut comp = Compiler::new(&type_env);
    let assembly = comp.compileModule(&module);

    assert_eq!(assembly.superCombinators[0].instructions, ~[PushFloat(3.), PushFloat(2.), DoubleAdd, Update(0), Unwind]);
}

#[test]
fn application() {
    let file =
r"add x y = primIntAdd x y
main = add 2 3";
    let mut parser = Parser::new(file.chars());
    let mut module = parser.module();
    let mut type_env = TypeEnvironment::new();
    type_env.typecheck_module(&mut module);
    let mut comp = Compiler::new(&type_env);
    let assembly = comp.compileModule(&module);

    assert_eq!(assembly.superCombinators[1].instructions, ~[PushInt(3), PushInt(2), PushGlobal(0), Mkap, Mkap, Eval, Update(0), Unwind]);
}

#[test]
fn compile_constructor() {
    let file =
r"primIntAdd 1 0 : []";
    let mut parser = Parser::new(file.chars());
    let mut expr = parser.expression_();
    let mut type_env = TypeEnvironment::new();
    type_env.typecheck(&mut expr);
    let mut comp = Compiler::new(&type_env);
    let instructions = comp.compileExpression(&expr);

    assert_eq!(instructions, ~[Pack(0, 0), PushInt(0), PushInt(1), Add, Pack(1, 2)]);
}

#[test]
fn compile_case() {
    let file =
r"case [primIntAdd 1 0] of
    : x xs -> x
    [] -> 2";
    let mut parser = Parser::new(file.chars());
    let mut expr = parser.expression_();
    let mut type_env = TypeEnvironment::new();
    type_env.typecheck(&mut expr);
    let mut comp = Compiler::new(&type_env);
    let instructions = comp.compileExpression(&expr);

    assert_eq!(instructions, ~[Pack(0, 0), PushInt(0), PushInt(1), Add, Pack(1, 2),
        CaseJump(1), Jump(9),
        CaseJump(0), Jump(13),
        Split(2), Push(0), Slide(2), Jump(17),
        Split(0), PushInt(2), Slide(0), Jump(17)]);
}

#[test]
fn compile_class_constraints() {
    let file =
r"class Test a where
    test :: a -> Int

instance Test Int where
    test x = x

main = test (primIntAdd 6 0)";
    let mut parser = Parser::new(file.chars());
    let mut module = parser.module();
    let mut type_env = TypeEnvironment::new();
    type_env.typecheck_module(&mut module);
    let mut comp = Compiler::new(&type_env);
    let assembly = comp.compileModule(&module);

    let main = &assembly.superCombinators[1];
    assert_eq!(main.name, ~"main");
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
    let mut parser = Parser::new(file.chars());
    let mut module = parser.module();
    let mut type_env = TypeEnvironment::new();
    type_env.typecheck_module(&mut module);
    let mut comp = Compiler::new(&type_env);
    let assembly = comp.compileModule(&module);

    let main = assembly.superCombinators[1];
    assert_eq!(main.name, ~"main");
    assert_eq!(main.instructions, ~[PushInt(6), Push(1), PushDictionaryMember(0), Mkap, Eval, Add, Update(0), Pop(2), Unwind]);
}

#[test]
fn compile_prelude() {
    let mut type_env = TypeEnvironment::new();
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let s  = File::open(path).read_to_end();
        let contents : &str = from_utf8(s);
        let mut parser = Parser::new(contents.chars()); 
        let mut module = parser.module();
        type_env.typecheck_module(&mut module);
        let mut compiler = Compiler::new(&type_env);
        compiler.compileModule(&mut module)
    };

    let file =
r"main = id (primIntAdd 2 0)";
    let mut parser = Parser::new(file.chars());
    let mut module = parser.module();
    type_env.typecheck_module(&mut module);
    let mut compiler = Compiler::new(&type_env);
    compiler.assemblies.push(&prelude);
    let assembly = compiler.compileModule(&module);

    let sc = &assembly.superCombinators[0];
    let id_index = prelude.superCombinators.iter().position(|sc| sc.name.equiv(& &"id")).unwrap();
    assert_eq!(sc.instructions, ~[PushInt(0), PushInt(2), Add, PushGlobal(id_index), Mkap, Eval, Update(0), Unwind]);
}

}
