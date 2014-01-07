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
    variables : HashMap<~str, Var>,
    globalIndex : int
}

impl Compiler {
    pub fn new() -> Compiler {
        Compiler { stackSize : 0, globals : HashMap::new(), variables : HashMap::new(), globalIndex : 0 }
    }

    pub fn compileModule(&mut self, module : &Module) {
        //TODO
        for bind in module.bindings.iter() {
            self.variables.insert(bind.name.clone(), GlobalVariable(self.globalIndex));
            self.globalIndex += 1;
            self.compileBinding(bind.arity, &bind.expression);
        }
    }
    fn compileBinding(&mut self, arity : int, expr : &Typed<Expr>) -> SuperCombinator {

        let mut comb = SuperCombinator::new();
        comb.arity = arity;
        match &expr.expr {
            &Lambda(_, _) => {
                self.compile(expr, &mut comb.instructions);
                comb.instructions.push(Update(0));
                comb.instructions.push(Pop(comb.arity));
                comb.instructions.push(Unwind);
            }
            _ => self.compile(expr, &mut comb.instructions)
       }
       comb
    }

    fn compile(&mut self, expr : &Typed<Expr>, instructions : &mut ~[Instruction]) {
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
            &Lambda(ref varname, ref body) => {
                self.variables.insert(varname.clone(), StackVariable(0));
                self.compile(*body, instructions);
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

#[test]
fn test_add() {
    let e = apply(identifier(~"primIntAdd"), apply(number(1), number(2)));
    let mut comp = Compiler::new();
    let comb = comp.compileBinding(0, &e);

    assert!(comb.instructions == ~[PushInt(1), PushInt(2), Add]);
}
