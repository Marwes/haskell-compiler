use std::fmt;
use std::rc::Rc;
use std::vec::from_fn;
use typecheck::TypeEnvironment;
use compiler::{Compiler, Assembly,
    Instruction, Add, Sub, Multiply, Divide, Remainder, IntEQ, IntLT, IntLE, IntGT, IntGE, Push, PushGlobal, PushInt, Mkap, Eval, Unwind, Update, Pop, Slide, Split, Pack, CaseJump, Jump, PushDictionary, PushDictionaryMember,
    SuperCombinator};
use parser::Parser;    

#[deriving(Clone)]
enum Node_<'a> {
    Application(Node<'a>, Node<'a>),
    Int(int),
    Combinator(&'a SuperCombinator),
    Indirection(Node<'a>),
    Constructor(u16, ~[Node<'a>]),
    Dictionary(&'a [uint])
}
#[deriving(Clone)]
struct Node<'a> {
    node: Rc<Node_<'a>>
}

impl <'a> Node<'a> {
    fn new(n : Node_<'a>) -> Node<'a> {
        Node { node: Rc::new(n) }
    }
    fn borrow<'b>(&'b self) -> &'b Node_<'a> {
        self.node.borrow()
    }
}
impl <'a> fmt::Default for Node<'a> {
    fn fmt(node: &Node<'a>, f: &mut fmt::Formatter) {
        write!(f.buf, "{}", *node.borrow())
    }
}
impl <'a, 'b> fmt::Default for &'b Node_<'a> {
    fn fmt(node: & &Node_<'a>, f: &mut fmt::Formatter) {
        write!(f.buf, "{}", **node)
    }
}
impl <'a> fmt::Default for Node_<'a> {
    fn fmt(node: &Node_<'a>, f: &mut fmt::Formatter) {
        match node {
            &Application(ref func, ref arg) => write!(f.buf, "({} {})", *func, *arg),
            &Int(i) => write!(f.buf, "{}", i),
            &Combinator(ref sc) => write!(f.buf, "{}", sc.name),
            &Indirection(ref n) => write!(f.buf, "(~> {})", *n),
            &Constructor(ref tag, ref args) => {
                write!(f.buf, "({}", *tag);
                for arg in args.iter() {
                    write!(f.buf, "{}",arg.borrow());
                }
                write!(f.buf, ")");
            }
            &Dictionary(ref dict) => write!(f.buf, "{:?}", dict)
        }
    }
}

pub struct VM<'a> {
    assembly : ~[Assembly],
    globals: ~[(uint, uint)],
    heap : ~[Node<'a>]
}

impl <'a> VM<'a> {
    pub fn new() -> VM {
        VM { assembly : ~[], heap : ~[], globals: ~[] }
    }

    ///Adds an assembly to the VM, adding entries to the global table as necessary
    pub fn add_assembly(&mut self, assembly: Assembly) {
        self.assembly.push(assembly);
        let assembly_index = self.assembly.len() - 1;
        let mut index = 0;
        for _ in self.assembly[self.assembly.len() - 1].superCombinators.iter() {
            self.globals.push((assembly_index, index));
            index += 1;
        }
    }

    pub fn evaluate(&'a self, code: &[Instruction]) -> Node_<'a> {
        let mut stack = ~[];
        self.execute(&mut stack, code);
        static evalCode : &'static [Instruction] = &[Eval];
        self.execute(&mut stack, evalCode);
        assert_eq!(stack.len(), 1);
        stack[0].borrow().clone()
    }

    pub fn execute(&'a self, stack : &mut ~[Node<'a>], code : &[Instruction]) {
        debug!("----------------------------");
        debug!("Entering frame with stack");
        for x in stack.iter() {
            debug!("{}", x.borrow());
        }
        debug!("");
        let mut i = 0;
        while i < code.len() {
            debug!("Executing instruction : {:?}", code[i]);
            match &code[i] {
                &Add => primitive(stack, |l, r| { l + r }),
                &Sub => primitive(stack, |l, r| { l - r }),
                &Multiply => primitive(stack, |l, r| { l * r }),
                &Divide => primitive(stack, |l, r| { l / r }),
                &Remainder => primitive(stack, |l, r| { l % r }),
                &IntEQ => primitive2(stack, |l, r| { if l == r { Constructor(0, ~[]) } else { Constructor(1, ~[]) } }),
                &IntLT => primitive2(stack, |l, r| { if l < r { Constructor(0, ~[]) } else { Constructor(1, ~[]) } }),
                &IntLE => primitive2(stack, |l, r| { if l <= r { Constructor(0, ~[]) } else { Constructor(1, ~[]) } }),
                &IntGT => primitive2(stack, |l, r| { if l > r { Constructor(0, ~[]) } else { Constructor(1, ~[]) } }),
                &IntGE => primitive2(stack, |l, r| { if l >= r { Constructor(0, ~[]) } else { Constructor(1, ~[]) } }),
                &PushInt(value) => { stack.push(Node::new(Int(value))); }
                &Push(index) => {
                    let x = stack[index].clone();
                    debug!("Pushed {}", x.borrow());
                    for j in range(0, stack.len()) {
                        debug!(" {}  {}", j, stack[j].borrow());
                    }
                    stack.push(x);
                }
                &PushGlobal(index) => {
                    let (assembly_index, index) = self.globals[index];
                    let sc = &self.assembly[assembly_index].superCombinators[index];
                    stack.push(Node::new(Combinator(sc)));
                }
                &Mkap => {
                    assert!(stack.len() >= 2);
                    let func = stack.pop();
                    let arg = stack.pop();
                    debug!("Mkap {} {}", func.borrow(), arg.borrow());
                    stack.push(Node::new(Application(func, arg)));
                }
                &Eval => {
                    static unwindCode : &'static [Instruction] = &[Unwind];
                    let mut newStack = ~[stack.pop()];
                    self.execute(&mut newStack, unwindCode);
                    stack.push(newStack.pop());
                }
                &Pop(num) => {
                    for _ in range(0, num) {
                        stack.pop();
                    }
                }
                &Update(index) => {
                    stack[index] = Node::new(Indirection(stack[stack.len() - 1].clone()));
                }
                &Unwind => {
                    let x = (*stack[stack.len() - 1].borrow()).clone();
                    debug!("Unwinding {}", x);
                    match x {
                        Application(func, _) => {
                            stack.push(func);
                            i -= 1;//Redo the unwind instruction
                        }
                        Combinator(comb) => {
                            if stack.len() - 1 < comb.arity as uint {
                                while stack.len() > 1 {
                                    stack.pop();
                                }
                            }
                            else {
                                for j in range(stack.len() - (comb.arity as uint) - 1, stack.len() - 1) {
                                    stack[j] = match stack[j].borrow() {
                                        &Application(_, ref arg) => arg.clone(),
                                        _ => fail!("Expected Application")
                                    };
                                }
                                let mut newStack = ~[];
                                for i in range(0, comb.arity as uint) {
                                    let index = stack.len() - i - 2;
                                    newStack.push(stack[index].clone());
                                }
                                
                                debug!("Called {}", comb.name);
                                for j in range(0, newStack.len()) {
                                    debug!(" {}  {}", j, newStack[j].borrow());
                                }
                                self.execute(&mut newStack, comb.instructions);
                                assert_eq!(newStack.len(), 1);
                                for _ in range(0, comb.arity + 1) {
                                    stack.pop();
                                }
                                stack.push(newStack.pop());
                            }
                        }
                        Indirection(node) => {
                            stack[stack.len() - 1] = node;
                            i -= 1;
                        }
                        _ => ()
                    }
                }
                &Slide(size) => {
                    let top = stack.pop();
                    for _ in range(0, size) {
                        stack.pop();
                    }
                    stack.push(top);
                }
                &Split(_) => {
                    let x = stack.pop();
                    match x.borrow() {
                        &Constructor(_, ref fields) => {
                            for field in fields.iter() {
                                stack.push(field.clone());
                            }
                        }
                        _ => fail!("Expected constructor in Split instruction")
                    }
                }
                &Pack(tag, arity) => {
                    let args = from_fn(arity as uint, |_| stack.pop());
                    stack.push(Node::new(Constructor(tag, args)));
                }
                &CaseJump(jump_tag) => {
                    match stack[stack.len() - 1].borrow() {
                        &Constructor(tag, _) => {
                            if jump_tag != tag as uint {
                                i += 1;//Skip the jump instruction
                            }
                        }
                        x => fail!("Expected constructor when executing CaseJump, got {}", x),
                    }
                }
                &Jump(to) => {
                    i = to - 1;
                }
                &PushDictionary(index) => {
                    stack.push(Node::new(Dictionary(self.assembly[0].instance_dictionaries[index])));
                }
                &PushDictionaryMember(index) => {
                    let sc = {
                        let dict = match stack[0].borrow() {
                            &Dictionary(ref x) => x,
                            x => fail!("Attempted to retrieve {} as dictionary", x)
                        };
                        let gi = dict[index];
                        let (assembly_index, i) = self.globals[gi];
                        &self.assembly[assembly_index].superCombinators[i]
                    };
                    stack.push(Node::new(Combinator(sc)));
                }
                //undefined => fail!("Use of undefined instruction {:?}", undefined)
            }
            i += 1;
        }
        debug!("End frame");
        debug!("--------------------------");
    }
}

fn primitive2(stack: &mut ~[Node], f: |int, int| -> Node_) {
    let l = stack.pop();
    let r = stack.pop();
    match (l.borrow(), r.borrow()) {
        (&Int(lhs), &Int(rhs)) => stack.push(Node::new(f(lhs, rhs))),
        (lhs, rhs) => fail!("Expected fully evaluted numbers in primitive instruction\n LHS: {}\nRHS: {} ", lhs, rhs)
    }
}
fn primitive(stack: &mut ~[Node], f: |int, int| -> int) {
    primitive2(stack, |l, r| Int(f(l, r)))
}

#[deriving(Eq)]
enum VMResult {
    IntResult(int),
    ConstructorResult(u16, ~[VMResult])
}

fn compile_iter<T : Iterator<char>>(iterator: T) -> Assembly {
    let mut parser = Parser::new(iterator);
    let mut module = parser.module();
    
    let mut typer = TypeEnvironment::new();
    typer.typecheck_module(&mut module);
    
    let mut compiler = Compiler::new(&typer);
    compiler.compileModule(&module)
}

fn extract_result(node: Node_) -> Option<VMResult> {
    match node {
        Constructor(tag, fields) => {
            let mut result = ~[];
            for field in fields.iter() {
                match extract_result(field.borrow().clone()) {
                    Some(x) => result.push(x),
                    None => return None
                }
            }
            Some(ConstructorResult(tag, result))
        }
        Int(i) => Some(IntResult(i)),
        x => {
            println!("Can't extract result {}", x);
            None
        }
    }
}

pub fn execute_main<T : Iterator<char>>(iterator: T) -> Option<VMResult> {
    let mut vm = VM::new();
    vm.add_assembly(compile_iter(iterator));
    let x = vm.assembly.iter().flat_map(|a| a.superCombinators.iter()).find(|sc| sc.name == ~"main");
    match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(sc.instructions);
            extract_result(result)
        }
        None => None
    }
}

#[cfg(test)]
mod tests {

use std::path::Path;
use std::io::File;
use std::str::from_utf8;
use typecheck::TypeEnvironment;
use compiler::Compiler;
use parser::Parser;
use vm::{VM, execute_main, extract_result, IntResult, ConstructorResult};

#[test]
fn test_primitive()
{
    assert_eq!(execute_main("main = primIntAdd 10 5".chars()), Some(IntResult(15)));
    assert_eq!(execute_main("main = primIntSubtract 7 (primIntMultiply 2 3)".chars()), Some(IntResult(1)));
    assert_eq!(execute_main("main = primIntDivide 10 (primIntRemainder 6 4)".chars()), Some(IntResult(5)));
    let s = 
r"data Bool = True | False
main = primIntLT 1 2";
    assert_eq!(execute_main(s.chars()), Some(ConstructorResult(0, ~[])));
}

#[test]
fn test_function()
{
    let module = 
r"mult2 x = primIntMultiply x 2

main = mult2 10";
    assert_eq!(execute_main(module.chars()), Some(IntResult(20)));

    let module2 = 
r"mult2 x = primIntMultiply x 2

add x y = primIntAdd y x

main = add 3 (mult2 10)";
    assert_eq!(execute_main(module2.chars()), Some(IntResult(23)));
}
#[test]
fn test_case()
{
    let module = 
r"mult2 x = primIntMultiply x 2

main = case [mult2 123, 0] of
    : x xs -> x
    [] -> 10";
    assert_eq!(execute_main(module.chars()), Some(IntResult(246)));
}

#[test]
fn test_data_types()
{
    let module = 
r"data Bool = True | False

test = False

main = case test of
    False -> 0
    True -> 1";
    assert_eq!(execute_main(module.chars()), Some(IntResult(0)));
}

#[test]
fn test_typeclasses_known_types()
{
    let module = 
r"data Bool = True | False

class Test a where
    test :: a -> Int

instance Test Int where
    test x = x

instance Test Bool where
    test x = case x of
        True -> 1
        False -> 0


main = primIntSubtract (test 5) (test True)";
    assert_eq!(execute_main(module.chars()), Some(IntResult(4)));
}

#[test]
fn test_typeclasses_unknown()
{
    let module = 
r"data Bool = True | False

class Test a where
    test :: a -> Int

instance Test Int where
    test x = x

instance Test Bool where
    test x = case x of
        True -> 1
        False -> 0

testAdd y = primIntAdd (test 5) (test y)

main = testAdd True";
    assert_eq!(execute_main(module.chars()), Some(IntResult(6)));
}

#[test]
fn test_run_prelude() {
    let mut type_env = TypeEnvironment::new();
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let s  = File::open(path).read_to_end();
        let contents : &str = from_utf8(s);
        let mut parser = Parser::new(contents.chars()); 
        let mut module = parser.module();
        type_env.typecheck_module(&mut module);
        let mut compiler = Compiler::new(&type_env);
        compiler.compileModule(&mut module)
    };

    let assembly = {
        let file =
r"add x y = primIntAdd x y
main = foldl add 0 [1,2,3,4]";
        let mut parser = Parser::new(file.chars());
        let mut module = parser.module();
        type_env.typecheck_module(&mut module);
        let mut compiler = Compiler::new(&type_env);
        compiler.assemblies.push(&prelude);
        compiler.compileModule(&module)
    };

    let mut vm = VM::new();
    vm.add_assembly(prelude);
    vm.add_assembly(assembly);
    let x = vm.assembly.iter().flat_map(|a| a.superCombinators.iter()).find(|sc| sc.name == ~"main");
    let result = match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(sc.instructions);
            extract_result(result)
        }
        None => None
    };
    assert_eq!(result, Some(IntResult(10)));
}

}
