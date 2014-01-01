use compiler::*;

mod typecheck;
mod compiler;


#[deriving(Clone)]
enum Node {
    Application(@Node, @Node),
    Int(int),
    Combinator(@SuperCombinator),
    Indirection(@Node)
}

struct VM {
    globals : ~[@SuperCombinator],
    heap : ~[Node]
}

impl VM {
    fn new() -> VM {
        VM { globals : ~[], heap : ~[] }
    }
    fn execute(&self, stack : &mut ~[@Node], code : &[Instruction]) {
        debug!("Entering frame");
        let mut i = 0;
        while i < code.len() {
            println!("Executing instruction : {:?}", code[i]);
            match &code[i] {
                &Add => {
                    let l = stack.pop();
                    let r = stack.pop();
                    println!("{:?} + {:?}", l, r);
                    match (*l, *r) {
                        (Int(lhs), Int(rhs)) => { stack.push(@Int(lhs + rhs)); }
                        _ => fail!("Expected fully evaluted numbers in Add instruction")
                    }
                }
                &Sub => {
                    let l = stack.pop();
                    let r = stack.pop();
                    match (*l, *r) {
                        (Int(lhs), Int(rhs)) => { stack.push(@Int(lhs - rhs)); }
                        _ => fail!("Expected fully evaluted numbers in Sub instruction")
                    }
                }
                &PushInt(value) => { stack.push(@Int(value)); }
                &Push(index) => {
                    let x = stack[index].clone();
                    stack.push(x);
                }
                &PushGlobal(index) => {
                    stack.push(@Combinator(self.globals[index]));
                }
                &Mkap => {
                    let func = stack.pop();
                    let arg = stack.pop();
                    stack.push(@Application(func, arg));
                }
                &Eval => {
                    static unwindCode : &'static [Instruction] = &[Unwind];
                    let mut newStack = ~[stack[stack.len() - 1]];
                    self.execute(&mut newStack, unwindCode);
                    assert!(newStack.len() == 1);
                    stack[stack.len() - 1] = newStack[0];
                }
                &Pop(num) => {
                    for _ in range(0, num) {
                        stack.pop();
                    }
                }
                &Update(index) => {
                    stack[index] = @Indirection(stack[stack.len() - 1]);
                }
                &Unwind => {
                    match *stack[stack.len() - 1] {
                        Application(func, _) => {
                            stack.push(func);
                            i -= 1;//Redo the unwind instruction
                        }
                        Combinator(comb) => {
                            for j in range(stack.len() - (comb.arity as uint) - 1, stack.len()) {
                                stack[j] = match stack[j] {
                                    @Application(_, arg) => arg,
                                    _ => fail!("Expected Application")
                                };
                            }
                            let mut newStack = ~[stack[stack.len() - 1]];
                            self.execute(&mut newStack, comb.instructions);
                            assert!(newStack.len() == 0);
                            for _ in range(0, comb.arity) {
                                stack.pop();
                            }
                            stack.push(newStack[0]);
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


