use std::hashmap::HashMap;
use typecheck::{Expr, Typed, Identifier, Apply, Number, Lambda, Let, identifier, apply, number, lambda, let_};
use parser::{Module, Class, Instance, Binding, DataDefinition, Constructor, TypeDeclaration,
    Pattern, ConstructorPattern, NumberPattern, IdentifierPattern, Alternative};
mod typecheck;

#[deriving(Eq)]
pub enum Instruction {
    Add,
    Sub,
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

struct Scope<'a, T> {
    variables: HashMap<~str, T>,
    parent: Option<&'a Scope<'a, T>>
}

impl <'a, T> Scope<'a, T> {
    
    fn new() -> Scope<T> {
        Scope { variables : HashMap::new(), parent : None }
    }

    fn insert(&mut self, identifier : ~str, value : T) {
        self.variables.insert(identifier, value);
    }

    fn find(&'a self, identifier : &str) -> Option<&'a T> {
       match self.variables.find_equiv(&identifier) {
            Some(var) => Some(var),
            None => match self.parent {
                Some(parent) => parent.find(identifier),
                None => None
            }
       }
    }

    fn child(&'a self) -> Scope<'a, T> {
        Scope { variables : HashMap::new(), parent : Some(self) }
    }
}

struct Assembly {
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

    pub fn compileModule(&mut self, module : &Module) {
        //TODO
        for bind in module.bindings.iter() {
            self.variables.insert(bind.name.clone(), GlobalVariable(self.globalIndex));
            self.globalIndex += 1;
            self.compileBinding(bind.arity, &bind.expression);
        }
    }
    fn compileBinding<'a>(&mut self, arity : int, expr : &Typed<Expr>) -> SuperCombinator {

        let mut comb = SuperCombinator::new();
        comb.arity = arity;
        let mut stack = CompilerNode { compiler: self, stack: Scope::new() };
        match &expr.expr {
            &Lambda(_, _) => {
                stack.compile(expr, &mut comb.instructions);
                comb.instructions.push(Update(0));
                comb.instructions.push(Pop(comb.arity));
                comb.instructions.push(Unwind);
            }
            _ => {
                stack.compile(expr, &mut comb.instructions);
                comb.instructions.push(Update(0));
                comb.instructions.push(Unwind);
            }
       }
       comb
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

    fn compile<'a>(&mut self, expr : &Typed<Expr>, instructions : &mut ~[Instruction]) {
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
                self.compile(*arg, instructions);
                self.compile(*func, instructions);
                instructions.push(Mkap);
                instructions.push(Eval);
            }
            &Lambda(ref varname, ref body) => {
                self.newStackVar(varname.clone());
                self.compile(*body, instructions);
            }
            &Let(ref bindings, ref body) => {
                for &(ref name, ref expr) in bindings.iter() {
                    self.newStackVar(name.clone());
                    self.compile(*expr, instructions);
                }
                self.compile(*body, instructions);
                instructions.push(Slide(bindings.len() as int));
            }
        }
    }
}


#[test]
fn test_add() {
    let e = apply(identifier(~"primIntAdd"), apply(number(1), number(2)));
    let mut comp = Compiler::new();
    let comb = comp.compileBinding(0, &e);

    assert!(comb.instructions == ~[PushInt(1), PushInt(2), Add]);
}
