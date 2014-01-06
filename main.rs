#[crate_id = "vm#0.0"];
#[crate_type = "bin"];
#[feature(managed_boxes, macro_rules, globs)];
extern mod extra;
use std::rc::Rc;
use compiler::{
    Instruction, Add, Sub, Push, PushGlobal, PushInt, Mkap, Eval, Unwind, Update, Pop, Slide,
    SuperCombinator};

mod compiler;
mod typecheck;
mod lexer;
mod parser;


#[deriving(Clone)]
enum Node {
    Application(Rc<Node>, Rc<Node>),
    Int(int),
    Combinator(Rc<SuperCombinator>),
    Indirection(Rc<Node>)
}

struct VM {
    globals : ~[Rc<SuperCombinator>],
    heap : ~[Node]
}

impl VM {
    fn new() -> VM {
        VM { globals : ~[], heap : ~[] }
    }
    fn execute(&self, stack : &mut ~[Rc<Node>], code : &[Instruction]) {
        debug!("Entering frame");
        let mut i = 0;
        while i < code.len() {
            println!("Executing instruction : {:?}", code[i]);
            match &code[i] {
                &Add => {
                    let l = stack.pop();
                    let r = stack.pop();
                    println!("{:?} + {:?}", l, r);
                    match (l.borrow(), r.borrow()) {
                        (&Int(lhs), &Int(rhs)) => { stack.push(Rc::new(Int(lhs + rhs))); }
                        _ => fail!("Expected fully evaluted numbers in Add instruction")
                    }
                }
                &Sub => {
                    let l = stack.pop();
                    let r = stack.pop();
                    match (l.borrow(), r.borrow()) {
                        (&Int(lhs), &Int(rhs)) => { stack.push(Rc::new(Int(lhs - rhs))); }
                        _ => fail!("Expected fully evaluted numbers in Sub instruction")
                    }
                }
                &PushInt(value) => { stack.push(Rc::new(Int(value))); }
                &Push(index) => {
                    let x = stack[index].clone();
                    stack.push(x);
                }
                &PushGlobal(index) => {
                    stack.push(Rc::new(Combinator(self.globals[index].clone())));
                }
                &Mkap => {
                    let func = stack.pop();
                    let arg = stack.pop();
                    stack.push(Rc::new(Application(func, arg)));
                }
                &Eval => {
                    static unwindCode : &'static [Instruction] = &[Unwind];
                    let mut newStack = ~[stack.pop()];
                    self.execute(&mut newStack, unwindCode);
                    assert!(newStack.len() == 1);
                    stack.push(newStack.pop());
                }
                &Pop(num) => {
                    for _ in range(0, num) {
                        stack.pop();
                    }
                }
                &Update(index) => {
                    stack[index] = Rc::new(Indirection(stack[stack.len() - 1].clone()));
                }
                &Unwind => {
                    match (*stack[stack.len() - 1].borrow()).clone() {
                        Application(func, _) => {
                            stack.push(func);
                            i -= 1;//Redo the unwind instruction
                        }
                        Combinator(comb_ptr) => {
                            let comb = comb_ptr.borrow();
                            for j in range(stack.len() - (comb.arity as uint) - 1, stack.len()) {
                                stack[j] = match stack[j].borrow() {
                                    &Application(_, ref arg) => arg.clone(),
                                    _ => fail!("Expected Application")
                                };
                            }
                            let mut newStack = ~[stack[stack.len() - 1].clone()];
                            self.execute(&mut newStack, comb.instructions);
                            assert!(newStack.len() == 0);
                            for _ in range(0, comb.arity) {
                                stack.pop();
                            }
                            stack.push(newStack.pop());
                        }
                        Indirection(node) => stack[stack.len() - 1] = node,
                        Int(_) => ()
                    }
                }
                &Slide(size) => {
                    for _ in range(0, size) {
                        stack.pop();
                    }
                }
            }
            i += 1;
        }
    }
}

fn main() {
    let instr = [PushInt(2), PushInt(3), Add];
    let vm = VM::new();
    let mut stack = ~[];
    vm.execute(&mut stack, instr);

    println!("Add : {:?}", stack);

}

#[test]
fn test()
{
    format!("{:?}", main);
}
