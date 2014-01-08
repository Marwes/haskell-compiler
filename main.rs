#[crate_id = "vm#0.0"];
#[crate_type = "bin"];
#[feature(managed_boxes, macro_rules, globs)];
extern mod extra;
use std::hashmap::HashMap;
use std::rc::Rc;
use std::path::Path;
use std::io::File;
use std::str::{from_utf8};
use typecheck::TypeEnvironment;
use compiler::{Compiler, Assembly,
    Instruction, Add, Sub, Multiply, Divide, Remainder, Push, PushGlobal, PushInt, Mkap, Eval, Unwind, Update, Pop, Slide,
    SuperCombinator};
use parser::Parser;    

mod compiler;
mod typecheck;
mod lexer;
mod parser;
mod module;

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

#[deriving(Clone)]
enum Node<'a> {
    Application(Rc<Node<'a>>, Rc<Node<'a>>),
    Int(int),
    Combinator(&'a SuperCombinator),
    Indirection(Rc<Node<'a>>)
}

struct VM<'a> {
    assembly : Assembly,
    heap : ~[Node<'a>]
}

impl <'a> VM<'a> {
    fn new() -> VM {
        VM { assembly : Assembly { superCombinators : ~[] }, heap : ~[] }
    }

    fn evaluate(&'a self, code: &[Instruction]) -> Node<'a> {
        let mut stack = ~[];
        self.execute(&mut stack, code);
        static evalCode : &'static [Instruction] = &[Eval];
        self.execute(&mut stack, evalCode);
        assert_eq!(stack.len(), 1);
        stack[0].borrow().clone()
    }

    fn execute(&'a self, stack : &mut ~[Rc<Node<'a>>], code : &[Instruction]) {
        debug!("----------------------------");
        debug!("Entering frame with stack");
        for x in stack.iter() {
            debug!("{:?}", x.borrow());
        }
        let mut i = 0;
        while i < code.len() {
            debug!("Executing instruction : {:?}", code[i]);
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
                    match &self.assembly.superCombinators[index] {
                        &(_, ref sc) => stack.push(Rc::new(Combinator(sc)))
                    }
                }
                &Mkap => {
                    let func = stack.pop();
                    let arg = stack.pop();
                    debug!("Mkap {:?} {:?}", func.borrow(), arg.borrow());
                    stack.push(Rc::new(Application(func, arg)));
                }
                &Eval => {
                    static unwindCode : &'static [Instruction] = &[Unwind];
                    let mut newStack = ~[stack.pop()];
                    self.execute(&mut newStack, unwindCode);
                    assert_eq!(newStack.len(), 1);
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
                            let comb = comb_ptr;
                            for j in range(stack.len() - (comb.arity as uint) - 1, stack.len() - 1) {
                                stack[j] = match stack[j].borrow() {
                                    &Application(_, ref arg) => arg.clone(),
                                    _ => fail!("Expected Application")
                                };
                            }
                            let mut newStack = ~[];
                            for i in range(0, comb.arity as uint) {
                                let index = stack.len() - comb.arity as uint + i - 1;
                                newStack.push(stack[index].clone());
                            }
                            self.execute(&mut newStack, comb.instructions);
                            assert_eq!(newStack.len(), 1);
                            for _ in range(0, comb.arity + 1) {
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
        debug!("End frame");
        debug!("--------------------------");
    }
}

fn primitive(stack: &mut ~[Rc<Node>], f: |int, int| -> int) {
    let l = stack.pop();
    let r = stack.pop();
    match (l.borrow(), r.borrow()) {
        (&Int(lhs), &Int(rhs)) => stack.push(Rc::new(Int(f(lhs, rhs)))),
        (lhs, rhs) => fail!("Expected fully evaluted numbers in primitive instruction\n LHS: {:?}\nRHS: {:?} ", lhs, rhs)
    }
}

fn main() {
    let arguments = std::os::args();
    match arguments {
        [_, expr_str] => {
            let mut parser = Parser::new(expr_str.chars());
            let mut expr = parser.expression_();

            let mut type_env = TypeEnvironment::new();
            type_env.typecheck(&mut expr);
            
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
            let mut vm = VM::new();
            vm.assembly = compiler.compileModule(&module);
            let x = vm.assembly.superCombinators.iter().find(|& &(ref name, _)| *name == ~"main");
            match x {
                Some(&(_, ref sc)) => {
                    assert!(sc.arity == 0);
                    let result = vm.evaluate(sc.instructions);
                    println!("{:?}", result);
                }
                None => ()
            }
        }
        _ => return println!("Expected one argument which is the expression or 2 arguments where the first is -l and the second the file to run (needs a main function)")
    }
}

#[test]
fn test()
{
    format!("{:?}", main);
}
