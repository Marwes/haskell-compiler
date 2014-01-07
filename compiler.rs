use std::hashmap::HashMap;
use typecheck::{identifier, apply, number, lambda, let_};
use module::{Type, TypeVariable, TypeOperator, Expr, Identifier, Number, Apply, Lambda, Let, Typed, Alternative, Module, Class, Instance, Binding, DataDefinition, Constructor, TypeDeclaration,
    Pattern, ConstructorPattern, NumberPattern, IdentifierPattern};
use parser::Parser;
use Scope;

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
    Slide(int),
}

enum Var {
    StackVariable(int),
    GlobalVariable(int)
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

pub struct Assembly {
    superCombinators: ~[(~str, SuperCombinator)]
}

impl Assembly {
    fn find(&self, name: &str) -> Option<Var> {
        let mut index = 0;
        for &(ref n, ref comb) in self.superCombinators.iter() {
            if name == *n {
                return Some(GlobalVariable(-1));
            }
            index += 1;
        }
        return None;
    }
}

pub struct Compiler {
    stackSize : int,
    globals : HashMap<~str, SuperCombinator>,
    variables: HashMap<~str, Var>,
    globalIndex : int
}


impl Compiler {
    pub fn new() -> Compiler {
        Compiler { stackSize : 0, globals : HashMap::new(), globalIndex : 0, variables: HashMap::new() }
    }

    pub fn compileModule(&mut self, module : &Module) -> Assembly {
        //TODO
        let mut superCombinators = ~[];
        for bind in module.bindings.iter() {
            self.variables.insert(bind.name.clone(), GlobalVariable(self.globalIndex));
            self.globalIndex += 1;
            let mut sc = self.compileBinding(bind.arity, &bind.expression);
            superCombinators.push((bind.name.clone(), sc));
        }
        Assembly { superCombinators: superCombinators }
    }
    fn compileBinding<'a>(&mut self, arity : int, expr : &Typed<Expr>) -> SuperCombinator {

        let mut comb = SuperCombinator::new();
        comb.arity = arity;
        let mut stack = CompilerNode { compiler: self, stack: Scope::new() };
        match &expr.expr {
            &Lambda(_, _) => {
                stack.compile(expr, &mut comb.instructions, false);
                comb.instructions.push(Update(0));
                comb.instructions.push(Pop(comb.arity));
                comb.instructions.push(Unwind);
            }
            _ => {
                stack.compile(expr, &mut comb.instructions, false);
                comb.instructions.push(Update(0));
                comb.instructions.push(Unwind);
            }
       }
       comb
    }
    pub fn compileExpression(&mut self, expr: &Typed<Expr>) -> ~[Instruction] {
        let mut stack = CompilerNode { compiler: self, stack: Scope::new() };
        let mut instructions = ~[];
        stack.compile(expr, &mut instructions, false);
        instructions
    }

}

struct CompilerNode<'a> {
    stack: Scope<'a, Var>,
    compiler: &'a mut Compiler
}

//CompilerNode are only used locally and the destructor are just to reduce the stack size
//so this should be safe(?)
#[unsafe_destructor]
impl <'a> Drop for CompilerNode<'a> {
    fn drop(&mut self) {
        self.compiler.stackSize -= self.stack.variables.len() as int;
    }
}

impl <'a> CompilerNode<'a> {
    
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

    fn child(&'a self) -> CompilerNode<'a> {
        CompilerNode { compiler: self.compiler, stack : self.stack.child() }
    }

    fn compile<'a>(&mut self, expr : &Typed<Expr>, instructions : &mut ~[Instruction], strict: bool) {
        match &expr.expr {
            &Identifier(ref name) => {
                match self.find(*name) {
                    None => fail!("Undefined variable " + *name),
                    Some(var) => {
                        match var {
                            &StackVariable(index) => instructions.push(Push(index)),
                            &GlobalVariable(index) => instructions.push(PushGlobal(index))
                        }
                    }
                }
            }
            &Number(num) => instructions.push(PushInt(num)),
            &Apply(ref func, ref arg) => {
                if !self.primitive(*func, *arg, instructions) {
                    self.compile(*arg, instructions, false);
                    self.compile(*func, instructions, strict);
                    instructions.push(Mkap);
                    if strict {
                        instructions.push(Eval);
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
                instructions.push(Slide(bindings.len() as int));
            }
        }
    }

    fn primitive(&mut self, func: &Typed<Expr>, arg: &Typed<Expr>, instructions: &mut ~[Instruction]) -> bool {
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
                                self.compile(*arg2, instructions, true);
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
            _ => false
        }
    }
}



#[test]
fn test_add() {
    let e = apply(apply(identifier(~"primIntAdd"), number(1)), number(2));
    let mut comp = Compiler::new();
    let instr = comp.compileExpression(&e);

    assert_eq!(instr, ~[PushInt(1), PushInt(2), Add]);
}

#[test]
fn test_apply() {
    let file =
r"add x y = primIntAdd x y
main = add 2 3";
    let mut parser = Parser::new(file.chars());
    let module = parser.module();
    let mut comp = Compiler::new();
    let assembly = comp.compileModule(&module);

    assert_eq!(assembly.superCombinators[1].n1().instructions, ~[PushInt(3), PushInt(2), PushGlobal(0), Mkap, Mkap, Update(0), Unwind]);
}
