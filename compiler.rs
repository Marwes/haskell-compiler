use std::hashmap::HashMap;
use module::{Type, TypeVariable, TypeOperator, Expr, Identifier, Number, Apply, Lambda, Let, Case, TypedExpr, Alternative, Module, Class, Instance, Binding, DataDefinition, Constructor, TypeDeclaration,
    Pattern, ConstructorPattern, NumberPattern, IdentifierPattern};
use Scope;
use typecheck::{TypeEnvironment};

#[cfg(test)]
use parser::Parser;
#[cfg(test)]
use typecheck::{identifier, apply, number, lambda, let_};

#[deriving(Eq)]
pub enum Instruction {
    Add,
    Sub,
    Multiply,
    Divide,
    Remainder,
    Push(int),
    PushGlobal(int),
    PushInt(int),
    Mkap,
    Eval,
    Unwind,
    Update(int),
    Pop(int),
    Slide(uint),
    Split(uint),
    Pack(u16, u16),
    CaseJump(uint),
    Jump(uint),
    PushDictionary(uint),
    PushDictionaryMember(uint),
}

enum Var {
    StackVariable(int),
    GlobalVariable(int),
    ConstructorVariable(u16, u16),
    ClassVariable(Type, TypeVariable)
}

pub struct SuperCombinator {
    arity : int,
    instructions : ~[Instruction]
}
impl SuperCombinator {
    fn new() -> SuperCombinator {
        SuperCombinator { arity : 0, instructions : ~[] }
    }
}

pub struct Assembly<'a> {
    superCombinators: ~[(~str, SuperCombinator)],
    instance_dictionaries: ~[~[uint]]
}

impl <'a> Assembly<'a> {
    fn find(&self, name: &str) -> Option<Var> {
        let mut index = 0;
        for &(ref n, _) in self.superCombinators.iter() {
            if name == *n {
                return Some(GlobalVariable(index));
            }
            index += 1;
        }
        return None;
    }
}

pub struct Compiler<'a> {
    type_env: &'a TypeEnvironment,
    class_dictionaries: HashMap<TypeOperator, ~[~str]>,
    instance_dictionaries: ~[(~[TypeOperator], ~[uint])],
    stackSize : int,
    globals : HashMap<~str, SuperCombinator>,
    variables: HashMap<~str, Var>,
    globalIndex : int,
}


impl <'a> Compiler<'a> {
    pub fn new(type_env: &'a TypeEnvironment) -> Compiler<'a> {
        let mut variables = HashMap::new();
        variables.insert(~"[]", ConstructorVariable(0, 0));
        variables.insert(~":", ConstructorVariable(1, 2));
        Compiler { type_env: type_env, class_dictionaries: HashMap::new(), instance_dictionaries: ~[],
            stackSize : 0, globals : HashMap::new(), globalIndex : 0, variables: variables }
    }

    pub fn compileModule(&mut self, module : &Module) -> Assembly {
        
        for dataDef in module.dataDefinitions.iter() {
            for ctor in dataDef.constructors.iter() {
                self.variables.insert(ctor.name.clone(), ConstructorVariable(ctor.tag as u16, ctor.arity as u16));
            }
        }
        
        for class in module.classes.iter() {
            let mut function_names = ~[];
            for decl in class.declarations.iter() {
                self.variables.insert(decl.name.clone(), ClassVariable(decl.typ.clone(), class.variable));
                function_names.push(decl.name.clone());
            }
            let op = TypeOperator { name: class.name.clone(), types: ~[TypeVariable(class.variable)] };
            self.class_dictionaries.insert(op, function_names);
        }

        let mut superCombinators = ~[];
        let mut instance_dictionaries = ~[];
        for instance in module.instances.iter() {
            for bind in instance.bindings.iter() {
                self.variables.insert(bind.name.clone(), GlobalVariable(self.globalIndex));
                self.globalIndex += 1;
                let sc = self.compileBinding(bind);
                superCombinators.push((bind.name.clone(), sc));
            }
        }
        for bind in module.bindings.iter() {
            self.variables.insert(bind.name.clone(), GlobalVariable(self.globalIndex));
            self.globalIndex += 1;
            let sc = self.compileBinding(bind);
            superCombinators.push((bind.name.clone(), sc));
        }
        Assembly { superCombinators: superCombinators, instance_dictionaries: instance_dictionaries }
    }
    fn compileBinding<'a>(&mut self, bind : &Binding) -> SuperCombinator {
        debug!("Compiling binding {}", bind.name);
        let mut comb = SuperCombinator::new();
        comb.arity = bind.arity;
        let mut stack = CompilerNode { compiler: self, stack: Scope::new(), constraints: bind.typeDecl.context };
        match &bind.expression.expr {
            &Lambda(_, _) => {
                stack.compile(&bind.expression, &mut comb.instructions, true);
                comb.instructions.push(Update(0));
                comb.instructions.push(Pop(bind.arity));
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
        let mut stack = CompilerNode { compiler: self, stack: Scope::new(), constraints: ~[] };
        let mut instructions = ~[];
        stack.compile(expr, &mut instructions, false);
        instructions
    }

}

struct CompilerNode<'a, 'b> {
    stack: Scope<'a, Var>,
    compiler: &'a mut Compiler<'b>,
    constraints: &'a [TypeOperator]
}

//CompilerNode are only used locally and the destructor are just to reduce the stack size
//so this should be safe(?)
#[unsafe_destructor]
impl <'a, 'b> Drop for CompilerNode<'a, 'b> {
    fn drop(&mut self) {
        self.compiler.stackSize -= self.stack.variables.len() as int;
    }
}

impl <'a, 'b> CompilerNode<'a, 'b> {
    
    fn find(&'a self, identifier : &str) -> Option<&'a Var> {
       match self.stack.find(identifier) {
            Some(var) => Some(var),
            None => self.compiler.variables.find_equiv(&identifier)
        }
    }

    fn newStackVar(&mut self, identifier : ~str) {
        self.stack.insert(identifier, StackVariable(self.compiler.stackSize));
        self.compiler.stackSize += 1;
    }
    fn removeStackVar(&mut self, identifier : &~str) {
        self.stack.variables.remove(identifier);
        self.compiler.stackSize -= 1;
    }

    fn child(&'a self) -> CompilerNode<'a, 'b> {
        CompilerNode { compiler: self.compiler, stack : self.stack.child(), constraints: self.constraints }
    }

    fn compile<'a>(&mut self, expr : &TypedExpr, instructions : &mut ~[Instruction], strict: bool) {
        debug!("Compiling {}", expr.expr);
        match &expr.expr {
            &Identifier(ref name) => {
                let maybe_new_dict = match self.find(*name) {
                    None => fail!("Undefined variable " + *name),
                    Some(var) => {
                        match var {
                            &StackVariable(index) => { instructions.push(Push(index)); None }
                            &GlobalVariable(index) => { instructions.push(PushGlobal(index)); None }
                            &ConstructorVariable(tag, arity) => { instructions.push(Pack(tag, arity)); None }
                            &ClassVariable(ref typ, ref var) => {
                                self.compile_instance_variable(expr, instructions, *name, typ, var)
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
            &Number(num) => instructions.push(PushInt(num)),
            &Apply(_, _) => {
                self.compile_apply(expr, instructions, strict);
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
                self.compile(*body, instructions, strict);
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

    fn compile_instance_variable(&self, expr: &TypedExpr, instructions: &mut ~[Instruction], name: &str, typ: &Type, var: &TypeVariable) -> Option<(~[TypeOperator], ~[uint])> {
        let actual_type = expr.typ.borrow().borrow();
        match try_find_instance_type(var, typ, actual_type.get()) {
            Some(typename) => {
                //We should be able to retrieve the instance directly
                let instance_fn_name = "#" + typename + name;
                match self.find(instance_fn_name) {
                    Some(&GlobalVariable(index)) => {
                        instructions.push(PushGlobal(index));
                    }
                    _ => fail!("Unregistered instance function {}", instance_fn_name)
                }
            }
            None => {
                match self.find("$dict") {
                    Some(&StackVariable(_)) => {
                        let constraints = self.compiler.type_env.find_constraints(typ);
                        //Push dictionary or member of dictionary
                        match self.push_dictionary_member(constraints, name) {
                            Some(index) => instructions.push(PushDictionaryMember(index)),
                            None => instructions.push(Push(0))
                        }
                    }
                    _ => {
                        //get dictionary index
                        //push dictionary
                        let dictionary_key = self.compiler.type_env.find_specialized_instances(name, typ);
                        let (index, dict) = self.find_dictionary_index(dictionary_key);
                        instructions.push(PushDictionary(index));
                        return dict;
                    }
                }
            }
        }
        None
    }

    fn push_dictionary_member(&self, constraints: &[TypeOperator], name: &str) -> Option<uint> {
        for c in constraints.iter() {
            match self.compiler.class_dictionaries.find(c) {
                Some(functions) => {
                    for ii in range(0, functions.len()) {
                        if functions[ii].equiv(&name) {
                            return Some(ii)
                        }
                    }
                }
                None => fail!("Undefined instance {:?}", c)
            }
        }
        None
    }

    fn find_dictionary_index(&self, constraints: &[TypeOperator]) -> (uint, Option<(~[TypeOperator], ~[uint])>) {
        
        let dict_len = self.compiler.instance_dictionaries.len();
        for ii in range(0, dict_len) {
            if self.compiler.instance_dictionaries[ii].n0_ref().equiv(&constraints) {
                return (ii, None);
            }
        }

        let mut function_indexes = ~[];
        for c in constraints.iter() {
            match self.compiler.class_dictionaries.find(c) {
                Some(functions) => {
                    for func in functions.iter() {
                        let f = "#" + c.name + *func;
                        match self.find(f) {
                            Some(&GlobalVariable(index)) => {
                                function_indexes.push(index as uint);
                            }
                            _ => fail!("Did not find function {}", f)
                        }
                    }
                }
                None => fail!("Could not find class dictionary {:?}", c)
            }
        }
        (dict_len, Some((constraints.to_owned(), function_indexes)))
    }

    fn compile_apply(&mut self, expr: &TypedExpr, instructions: &mut ~[Instruction], strict: bool) {
        match &expr.expr {
            &Apply(ref func, ref arg) => {
                if !self.primitive(*func, *arg, instructions) {
                    self.compile(*arg, instructions, false);
                    self.compile_apply(*func, instructions, false);
                    match &instructions[instructions.len() - 1] {
                        &Pack(_, _) => (),//The function was only the pack instruction so to do Mkap
                        _ => instructions.push(Mkap)
                    }
                    if strict {
                        instructions.push(Eval);
                    }
                }
            }
            _ => self.compile(expr, instructions, strict)
        }
    }

    fn primitive(&mut self, func: &TypedExpr, arg: &TypedExpr, instructions: &mut ~[Instruction]) -> bool {
        match &func.expr {
            &Apply(ref prim_func, ref arg2) => {
                match &prim_func.expr {
                    &Identifier(ref name) => {
                        let maybeOP = match *name {
                            ~"primIntAdd" => Some(Add),
                            ~"primIntSubtract" => Some(Sub),
                            ~"primIntMultiply" => Some(Multiply),
                            ~"primIntDivide" => Some(Divide),
                            ~"primIntRemainder" => Some(Remainder),
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
            _ => false
        }
    }

    fn compile_pattern(&self, pattern: &Pattern, branches: &mut ~[uint], instructions: &mut ~[Instruction]) {
        //TODO this is unlikely to work with nested patterns currently
        match pattern {
            &ConstructorPattern(ref name, ref patterns) => {
                match self.find(*name) {
                    Some(&ConstructorVariable(tag, _)) => {
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

    fn find_instance_member(&self, function_name: &str) -> Option<uint> {
        for constraint in self.constraints.iter() {
            let x = self.compiler.class_dictionaries.find(constraint).map_or(None,
                |functions:&~[~str]| {
                for i in range(0, functions.len()) {
                    if functions[i].equiv(&function_name) {
                        return Some(i);
                    }
                }
                None
            });
            if x != None {
                return x;
            }
        }
        None
    }

}

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


#[test]
fn test_add() {
    let e = apply(apply(identifier(~"primIntAdd"), number(1)), number(2));
    let mut type_env = TypeEnvironment::new();
    let mut comp = Compiler::new(&type_env);
    let instr = comp.compileExpression(&e);

    assert_eq!(instr, ~[PushInt(2), PushInt(1), Add]);
}

#[test]
fn test_apply() {
    let file =
r"add x y = primIntAdd x y
main = add 2 3";
    let mut parser = Parser::new(file.chars());
    let module = parser.module();
    let mut type_env = TypeEnvironment::new();
    let mut comp = Compiler::new(&type_env);
    let assembly = comp.compileModule(&module);

    assert_eq!(assembly.superCombinators[1].n1().instructions, ~[PushInt(3), PushInt(2), PushGlobal(0), Mkap, Mkap, Eval, Update(0), Unwind]);
}

#[test]
fn test_compile_constructor() {
    let file =
r"1 : []";
    let mut parser = Parser::new(file.chars());
    let expr = parser.expression_();
    let mut type_env = TypeEnvironment::new();
    let mut comp = Compiler::new(&type_env);
    let instructions = comp.compileExpression(&expr);

    assert_eq!(instructions, ~[Pack(0, 0), PushInt(1), Pack(1, 2)]);
}

#[test]
fn test_compile_case() {
    let file =
r"case [1] of
    : x xs -> x
    [] -> 2";
    let mut parser = Parser::new(file.chars());
    let expr = parser.expression_();
    let mut type_env = TypeEnvironment::new();
    let mut comp = Compiler::new(&type_env);
    let instructions = comp.compileExpression(&expr);

    assert_eq!(instructions, ~[Pack(0, 0), PushInt(1), Pack(1, 2),
        CaseJump(1), Jump(7),
        CaseJump(0), Jump(11),
        Split(2), Push(0), Slide(2), Jump(15),
        Split(0), PushInt(2), Slide(0), Jump(15)]);
}

#[test]
fn test_compile_class_constraints() {
    let file =
r"class Test a where
    test :: a -> Int

instance Test Int where
    test x = x

main = test 6";
    let mut parser = Parser::new(file.chars());
    let mut module = parser.module();
    let mut type_env = TypeEnvironment::new();
    type_env.typecheck_module(&mut module);
    let mut comp = Compiler::new(&type_env);
    let assembly = comp.compileModule(&module);

    let (ref name, ref main) = assembly.superCombinators[1];
    assert_eq!(name, &~"main");
    assert_eq!(main.instructions, ~[PushInt(6), PushGlobal(0), Mkap, Eval, Update(0), Unwind]);
}

#[test]
fn test_compile_class_constraints_unknown() {
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

    let (ref name, ref main) = assembly.superCombinators[1];
    assert_eq!(name, &~"main");
    assert_eq!(main.instructions, ~[PushInt(6), Push(0), PushDictionary(0), Mkap, Eval, Add, Update(0), Pop(1), Unwind]);
}
