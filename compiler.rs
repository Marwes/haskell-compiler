use std::hashmap::HashMap;
use typecheck::{Expr, TypedExpr, Identifier, Apply, Number, Lambda, Let};
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

struct Compiler {
    stackSize : int,
    globals : HashMap<~str, SuperCombinator>,
    variables : HashMap<~str, Var>,
    globalIndex : int
}

impl Compiler {
    fn new() -> Compiler {
        Compiler { stackSize : 0, globals : HashMap::new(), variables : HashMap::new(), globalIndex : 0 }
    }

    fn compileModule(&mut self) {
        //TODO
        let bindings : ~[(~str, int, TypedExpr)] = ~[];
        for &(ref identifier, arity, ref expr) in bindings.iter() {
            self.variables.insert(identifier.clone(), GlobalVariable(self.globalIndex));
            self.globalIndex += 1;
            self.compileBinding(arity, expr);
        }
    }
    fn compileBinding(&mut self, arity : int, expr : &TypedExpr) -> SuperCombinator {

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

fn identifier(i : ~str) -> TypedExpr {
    TypedExpr::new(Identifier(i))
}

fn lambda(arg : ~str, body : TypedExpr) -> TypedExpr {
    TypedExpr::new(Lambda(arg, ~body))
}
fn number(i : int) -> TypedExpr {
    TypedExpr::new(Number(i))
}
fn apply(func : TypedExpr, arg : TypedExpr) -> TypedExpr {
    TypedExpr::new(Apply(~func, ~arg))
}
fn let_(bindings : ~[(~str, ~TypedExpr)], expr : TypedExpr) -> TypedExpr {
    TypedExpr::new(Let(bindings, ~expr))
}

#[test]
fn test_add() {
    let e = apply(identifier(~"primIntAdd"), apply(number(1), number(2)));
    let mut comp = Compiler::new();
    let comb = comp.compileBinding(0, &e);

    assert!(comb.instructions == ~[PushInt(1), PushInt(2), Add]);
}
