#[crate_id = "vm#0.0"];
#[crate_type = "bin"];
#[feature(managed_boxes, macro_rules, globs)];
extern mod extra;
use std::rc::Rc;
use std::path::Path;
use std::io::File;
use std::str::{from_utf8};
use compiler::{Compiler,
    Instruction, Add, Sub, Multiply, Divide, Remainder, Push, PushGlobal, PushInt, Mkap, Eval, Unwind, Update, Pop, Slide,
    SuperCombinator};
use parser::Parser;    

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
                &Add => primitive(stack, |l, r| { l + r }),
                &Sub => primitive(stack, |l, r| { l - r }),
                &Multiply => primitive(stack, |l, r| { l * r }),
                &Divide => primitive(stack, |l, r| { l / r }),
                &Remainder => primitive(stack, |l, r| { l % r }),
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

fn primitive(stack: &mut ~[Rc<Node>], f: |int, int| -> int) {
    let l = stack.pop();
    let r = stack.pop();
    match (l.borrow(), r.borrow()) {
        (&Int(lhs), &Int(rhs)) => stack.push(Rc::new(Int(f(lhs, rhs)))),
        _ => fail!("Expected fully evaluted numbers in Add instruction")
    }
}

fn main() {
    let arguments = std::os::args();
    match arguments {
        [_, expr_str] => {
            let mut parser = Parser::new(expr_str.chars());
            let expr = parser.expression_();
            
            let mut compiler = Compiler::new();
            let instr = compiler.compileExpression(&expr);

            let vm = VM::new();
            let mut stack = ~[];
            vm.execute(&mut stack, instr);
            println!("{:?}", stack[0].borrow());
        }
        [_, ~"-l", filename] => {
            let path = &Path::new(filename);
            let s  = File::open(path).read_to_end();
            let contents : &str = from_utf8(s);
            
            let mut parser = Parser::new(contents.chars());
            let module = parser.module();
            
            let mut compiler = Compiler::new();
            compiler.compileModule(&module);
        }
        _ => return println!("Expected one argument which is the expression or 2 arguments where the first is -l and the second the file to run (needs a main function)")
    }
}

#[test]
fn test()
{
    format!("{:?}", main);
}
