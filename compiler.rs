use std::hashmap::HashMap;
use typecheck::*;
mod typecheck;

pub enum Instruction {
    Add,
    Sub,
    Push(int),
    PushGlobal(int),
    PushInt(int),
    Mkap,
    Eval,
    Unwind,
    Slide(int),
}

enum Var {
    StackVariable(int),
    GlobalVariable(int)
}

struct SuperCombinator {
    arity : int,
    instructions : ~[Instruction]
}
impl SuperCombinator {
    fn new() -> SuperCombinator {
        SuperCombinator { arity : 0, instructions : ~[] }
    }
}

struct Scope {
    variables : HashMap<~str, Var>
}

struct ScopedLookup {
    scopes : ~[Scope],
}

impl ScopedLookup {
    fn new_scope(&mut self, scope : Scope) {
        self.scopes.push(scope);
    }
    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn find(&self, identifier : &str) -> Option<Var> {
        for scope in self.scopes.rev_iter() {
           match scope.variables.find_equiv(&identifier) {
                Some(var) => { return Some(*var); }
                None => {}
           }
        }
        return None
    }
}

struct Compiler {
    stackSize : int,
    globals : HashMap<~str, SuperCombinator>,
    variables : HashMap<~str, Var>,
    globalIndex : int
}

impl Compiler {
    fn compileBinding(&mut self, identifier : ~str, expr : &TypedExpr) {
        self.variables.insert(identifier.clone(), GlobalVariable(self.globalIndex));
        self.globalIndex += 1;

        let mut comb = SuperCombinator::new();
        match &expr.expr {
            &Lambda(_, _) => {
                
            }
            _ => self.compile(expr, &mut comb.instructions)
       }
       self.globals.insert(identifier, comb);
    }

    fn compile(&mut self, expr : &TypedExpr, instructions : &mut ~[Instruction]) {
        match &expr.expr {
            &Identifier(ref name) => {
                match self.variables.find(name) {
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
            &Lambda(_, _) => {
                fail!("Can't compile a lambda");
            }
            &Let(ref bindings, ref body) => {
                for &(ref name, ref expr) in bindings.iter() {
                    self.variables.insert(name.clone(), StackVariable(self.stackSize));
                    self.stackSize += 1;
                    self.compile(*expr, instructions);
                }
                self.compile(*body, instructions);
                instructions.push(Slide(bindings.len() as int));
                self.stackSize -= bindings.len() as int;
            }
        }
    }
}
