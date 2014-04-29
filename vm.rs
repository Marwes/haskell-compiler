use std::fmt;
use std::rc::Rc;
use std::cell::{Ref, RefCell};
use std::path::Path;
use std::io::File;
use typecheck::TypeEnvironment;
use compiler::*;
use parser::Parser;
use core::translate::translate_module;
use lambda_lift::do_lambda_lift;
use renamer::rename_module;
use vm::primitive::{PrimFun, get_primitive};

enum Node_<'a> {
    Application(Node<'a>, Node<'a>),
    Int(int),
    Float(f64),
    Char(char),
    Combinator(&'a SuperCombinator),
    Indirection(Node<'a>),
    Constructor(u16, Vec<Node<'a>>),
    Dictionary(&'a [uint]),
    PrimitiveFunction(uint, PrimFun)
}
impl <'a> Clone for Node_<'a> {
    fn clone(&self) -> Node_<'a> {
        match self {
            &Application(ref func, ref arg) => Application(func.clone(), arg.clone()),
            &Int(i) => Int(i),
            &Float(i) => Float(i),
            &Char(c) => Char(c),
            &Combinator(sc) => Combinator(sc),
            &Indirection(ref n) => Indirection(n.clone()),
            &Constructor(ref tag, ref args) => Constructor(tag.clone(), args.clone()),
            &Dictionary(dict) => Dictionary(dict),
            &PrimitiveFunction(arity, f) => PrimitiveFunction(arity, f)
        }
    }
}

#[deriving(Clone)]
struct Node<'a> {
    node: Rc<RefCell<Node_<'a>>>
}

impl <'a> Node<'a> {
    fn new(n : Node_<'a>) -> Node<'a> {
        Node { node: Rc::new(RefCell::new(n)) }
    }
    fn borrow<'b>(&'b self) -> Ref<'b, Node_<'a>> {
        (*self.node).borrow()
    }
}
impl <'a> fmt::Show for Node<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f.buf, "{}", *self.borrow())
    }
}
impl <'a> fmt::Show for Node_<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Application(ref func, ref arg) => write!(f.buf, "({} {})", *func, *arg),
            &Int(i) => write!(f.buf, "{}", i),
            &Float(i) => write!(f.buf, "{}", i),
            &Char(c) => write!(f.buf, "'{}'", c),
            &Combinator(ref sc) => write!(f.buf, "{}", sc.name),
            &Indirection(ref n) => write!(f.buf, "(~> {})", *n),
            &Constructor(ref tag, ref args) => {
                let cons = args;
                if cons.len() > 0 {
                    match *cons.get(0).borrow() {
                        Char(_) => {
                            fn print_string<'a>(f: &mut fmt::Formatter, cons: &Vec<Node<'a>>) -> fmt::Result {
                                if cons.len() >= 2 {
                                    match *cons.get(0).borrow() {
                                        Char(c) =>  { try!(write!(f.buf, "{}", c)); },
                                        _ => ()
                                    }
                                    match *cons.get(1).borrow() {
                                        Constructor(_, ref args2) => return print_string(f, args2),
                                        _ => ()
                                    }
                                }
                                Ok(())
                            }
                            try!(write!(f.buf, "\""));
                            print_string(f, cons);
                            write!(f.buf, "\"")
                        }
                        _ => {
                            //Print a normal constructor
                            try!(write!(f.buf, "\\{{}", *tag));
                            for arg in args.iter() {
                                try!(write!(f.buf, " {}", *arg.borrow()));
                            }
                            write!(f.buf, "\\}")
                        }
                    }
                }
                else {
                    //Print a normal constructor
                    try!(write!(f.buf, "\\{{}", *tag));
                    for arg in args.iter() {
                        try!(write!(f.buf, " {}", *arg.borrow()));
                    }
                    write!(f.buf, "\\}")
                }
            }
            &Dictionary(ref dict) => write!(f.buf, "{:?}", dict),
            &PrimitiveFunction(..) => write!(f.buf, "<extern function>")
        }
    }
}

pub struct VM<'a> {
    assembly : Vec<Assembly>,
    globals: Vec<(uint, uint)>,
    heap : Vec<Node<'a>>,
}

impl <'a> VM<'a> {
    pub fn new() -> VM {
        VM { assembly : Vec::new(), heap : Vec::new(), globals: Vec::new() }
    }

    ///Adds an assembly to the VM, adding entries to the global table as necessary
    pub fn add_assembly(&mut self, assembly: Assembly) -> uint {
        self.assembly.push(assembly);
        let assembly_index = self.assembly.len() - 1;
        let mut index = 0;
        for _ in self.assembly.last().unwrap().superCombinators.iter() {
            self.globals.push((assembly_index, index));
            index += 1;
        }
        assembly_index
    }

    pub fn evaluate(&'a self, code: &[Instruction], assembly_id: uint) -> Node_<'a> {
        let mut stack = Vec::new();
        self.execute(&mut stack, code, assembly_id);
        self.deepseq(stack, assembly_id)
    }
    fn deepseq(&'a self, mut stack: Vec<Node<'a>>, assembly_id: uint) -> Node_<'a> {
        static evalCode : &'static [Instruction] = &[Eval];
        self.execute(&mut stack, evalCode, assembly_id);
        match *stack.get(0).borrow() {
            Constructor(tag, ref vals) => {
                let mut ret = Vec::new();
                for v in vals.iter() {
                    let s = vec!(v.clone());
                    let x = self.deepseq(s, assembly_id);
                    ret.push(Node::new(x));
                }
                Constructor(tag, ret)
            }
            _ => stack.get(0).borrow().clone()
        }
    }

    pub fn execute(&'a self, stack: &mut Vec<Node<'a>>, code: &[Instruction], assembly_id: uint) {
        debug!("----------------------------");
        debug!("Entering frame with stack");
        for x in stack.iter() {
            debug!("{}", *x.borrow());
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
                &IntEQ => primitive_int(stack, |l, r| { if l == r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                &IntLT => primitive_int(stack, |l, r| { if l < r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                &IntLE => primitive_int(stack, |l, r| { if l <= r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                &IntGT => primitive_int(stack, |l, r| { if l > r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                &IntGE => primitive_int(stack, |l, r| { if l >= r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                &DoubleAdd => primitive_float(stack, |l, r| { Float(l + r) }),
                &DoubleSub => primitive_float(stack, |l, r| { Float(l - r) }),
                &DoubleMultiply => primitive_float(stack, |l, r| { Float(l * r) }),
                &DoubleDivide => primitive_float(stack, |l, r| { Float(l / r) }),
                &DoubleRemainder => primitive_float(stack, |l, r| { Float(l % r) }),
                &DoubleEQ => primitive_float(stack, |l, r| { if l == r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                &DoubleLT => primitive_float(stack, |l, r| { if l < r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                &DoubleLE => primitive_float(stack, |l, r| { if l <= r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                &DoubleGT => primitive_float(stack, |l, r| { if l > r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                &DoubleGE => primitive_float(stack, |l, r| { if l >= r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                &IntToDouble => {
                    let top = stack.pop().unwrap();
                    stack.push(match *top.borrow() {
                        Int(i) => Node::new(Float(i as f64)),
                        _ => fail!("Excpected Int in Int -> Double cast")
                    });
                }
                &DoubleToInt => {
                    let top = stack.pop().unwrap();
                    stack.push(match *top.borrow() {
                        Float(f) => Node::new(Int(f as int)),
                        _ => fail!("Excpected Double in Double -> Int cast")
                    });
                }
                &PushInt(value) => { stack.push(Node::new(Int(value))); }
                &PushFloat(value) => { stack.push(Node::new(Float(value))); }
                &PushChar(value) => { stack.push(Node::new(Char(value))); }
                &Push(index) => {
                    let x = stack.get(index).clone();
                    debug!("Pushed {}", *x.borrow());
                    for j in range(0, stack.len()) {
                        debug!(" {}  {}", j, *stack.get(j).borrow());
                    }
                    stack.push(x);
                }
                &PushGlobal(index) => {
                    let &(assembly_index, index) = self.globals.get(index);
                    let sc = &self.assembly.get(assembly_index).superCombinators[index];
                    stack.push(Node::new(Combinator(sc)));
                }
                &PushPrimitive(index) => {
                    let (arity, f) = get_primitive(index);
                    stack.push(Node::new(PrimitiveFunction(arity, f)));
                }
                &Mkap => {
                    assert!(stack.len() >= 2);
                    let func = stack.pop().unwrap();
                    let arg = stack.pop().unwrap();
                    debug!("Mkap {} {}", *func.borrow(), *arg.borrow());
                    stack.push(Node::new(Application(func, arg)));
                }
                &Eval => {
                    static unwindCode : &'static [Instruction] = &[Unwind];
                    let mut newStack = vec!(stack.pop().unwrap());
                    self.execute(&mut newStack, unwindCode, assembly_id);
                    stack.push(newStack.pop().unwrap());
                }
                &Pop(num) => {
                    for _ in range(0, num) {
                        stack.pop();
                    }
                }
                &Update(index) => {
                    *stack.get_mut(index) = Node::new(Indirection(stack.last().unwrap().clone()));
                }
                &Unwind => {
                    fn unwind<'a>(arity: uint, stack: &mut Vec<Node<'a>>, f: |&mut Vec<Node<'a>>| -> Node<'a>) {
                        if stack.len() - 1 < arity {
                            while stack.len() > 1 {
                                stack.pop();
                            }
                        }
                        else {
                            for j in range(stack.len() - arity - 1, stack.len() - 1) {
                                *stack.get_mut(j) = match *stack.get(j).borrow() {
                                    Application(_, ref arg) => arg.clone(),
                                    _ => fail!("Expected Application")
                                };
                            }
                            let value = {
                                let mut new_stack = Vec::new();
                                for i in range(0, arity) {
                                    let index = stack.len() - i - 2;
                                    new_stack.push(stack.get(index).clone());
                                }
                                f(&mut new_stack)
                            };
                            for _ in range(0, arity + 1) {
                                stack.pop();
                            }
                            stack.push(value);
                        }
                    }
                    let x = (*stack.last().unwrap().borrow()).clone();
                    debug!("Unwinding {}", x);
                    match x {
                        Application(func, _) => {
                            stack.push(func);
                            i -= 1;//Redo the unwind instruction
                        }
                        Combinator(comb) => {
                            unwind(comb.arity, stack, |new_stack| {
                                self.execute(new_stack, comb.instructions, comb.assembly_id);
                                new_stack.pop().unwrap()
                            });
                            i -= 1;
                        }
                        PrimitiveFunction(arity, func) => {
                            unwind(arity, stack, |new_stack| func(self, new_stack.as_slice()));
                            i -= 1;
                        }
                        Indirection(node) => {
                            *stack.mut_last().unwrap() = node;
                            i -= 1;
                        }
                        _ => ()
                    }
                }
                &Slide(size) => {
                    let top = stack.pop().unwrap();
                    for _ in range(0, size) {
                        stack.pop();
                    }
                    stack.push(top);
                }
                &Split(_) => {
                    match *stack.pop().unwrap().borrow() {
                        Constructor(_, ref fields) => {
                            for field in fields.iter() {
                                stack.push(field.clone());
                            }
                        }
                        _ => fail!("Expected constructor in Split instruction")
                    }
                }
                &Pack(tag, arity) => {
                    let mut args = Vec::new();
                    for _ in range(0, arity) {
                        args.push(stack.pop().unwrap());
                    }
                    stack.push(Node::new(Constructor(tag, args)));
                }
                &JumpFalse(address) => {
                    match *stack.last().unwrap().borrow() {
                        Constructor(0, _) => (),
                        Constructor(1, _) => i = address - 1,
                        _ => ()
                    }
                    stack.pop();
                }
                &CaseJump(jump_tag) => {
                    let jumped = match *stack.last().unwrap().borrow() {
                        Constructor(tag, _) => {
                            if jump_tag == tag as uint {
                                i += 1;//Skip the jump instruction ie continue to the next test
                                true
                            }
                            else {
                                false
                            }
                        }
                        ref x => fail!("Expected constructor when executing CaseJump, got {}", *x),
                    };
                    if !jumped {
                        stack.pop();
                    }
                }
                &Jump(to) => {
                    i = to - 1;
                }
                &PushDictionary(index) => {
                    let assembly = self.assembly.get(assembly_id);
                    let dict : &[uint] = assembly.instance_dictionaries[index];
                    stack.push(Node::new(Dictionary(dict)));
                }
                &PushDictionaryMember(index) => {
                    let sc = {
                        let x = stack.get(0).borrow();
                        let dict = match *x {
                            Dictionary(ref x) => x,
                            ref x => fail!("Attempted to retrieve {} as dictionary", *x)
                        };
                        let gi = dict[index];
                        let &(assembly_index, i) = self.globals.get(gi);
                        &self.assembly.get(assembly_index).superCombinators[i]
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

fn primitive_int(stack: &mut Vec<Node>, f: |int, int| -> Node_) {
    let l = stack.pop().unwrap();
    let r = stack.pop().unwrap();
    match (&*l.borrow(), &*r.borrow()) {
        (&Int(lhs), &Int(rhs)) => stack.push(Node::new(f(lhs, rhs))),
        (lhs, rhs) => fail!("Expected fully evaluted numbers in primitive instruction\n LHS: {}\nRHS: {} ", lhs, rhs)
    }
}
fn primitive_float(stack: &mut Vec<Node>, f: |f64, f64| -> Node_) {
    let l = stack.pop().unwrap();
    let r = stack.pop().unwrap();
    match (&*l.borrow(), &*r.borrow()) {
        (&Float(lhs), &Float(rhs)) => stack.push(Node::new(f(lhs, rhs))),
        (lhs, rhs) => fail!("Expected fully evaluted numbers in primitive instruction\n LHS: {}\nRHS: {} ", lhs, rhs)
    }
}
fn primitive(stack: &mut Vec<Node>, f: |int, int| -> int) {
    primitive_int(stack, |l, r| Int(f(l, r)))
}

#[deriving(Eq, Show)]
enum VMResult {
    IntResult(int),
    DoubleResult(f64),
    ConstructorResult(u16, Vec<VMResult>)
}

fn compile_iter<T : Iterator<char>>(iterator: T) -> Assembly {
    let mut parser = Parser::new(iterator);
    let mut module = rename_module(parser.module());
    
    let mut typer = TypeEnvironment::new();
    typer.typecheck_module(&mut module);
    let core_module = do_lambda_lift(translate_module(module));
    
    let mut compiler = Compiler::new(&typer);
    compiler.compileModule(&core_module)
}

pub fn compile_file(filename: &str) -> Assembly {
    let path = &Path::new(filename);
    let contents = File::open(path).read_to_str().unwrap();
    compile_iter(contents.chars())
}

fn extract_result(node: Node_) -> Option<VMResult> {
    match node {
        Constructor(tag, fields) => {
            let mut result = Vec::new();
            for field in fields.iter() {
                match extract_result((*field.borrow()).clone()) {
                    Some(x) => result.push(x),
                    None => return None
                }
            }
            Some(ConstructorResult(tag, result))
        }
        Int(i) => Some(IntResult(i)),
        Float(i) => Some(DoubleResult(i)),
        x => {
            println!("Can't extract result {}", x);
            None
        }
    }
}

pub fn execute_main<T : Iterator<char>>(iterator: T) -> Option<VMResult> {
    let mut vm = VM::new();
    vm.add_assembly(compile_iter(iterator));
    let x = vm.assembly.iter().flat_map(|a| a.superCombinators.iter()).find(|sc| sc.name.name == ~"main");
    match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(sc.instructions, sc.assembly_id);
            extract_result(result)
        }
        None => None
    }
}

mod primitive {

    use vm::{VM, Node, Int};
    use compiler::{Instruction, Eval};

    pub fn get_primitive(i: uint) -> (uint, PrimFun) {
        match i {
            0 => (1, error),
            1 => (2, seq),
            _ => fail!("undefined primitive")
        }
    }

    pub type PrimFun = extern "Rust" fn <'a>(&'a VM<'a>, &[Node<'a>]) -> Node<'a>;

    fn error<'a>(vm: &'a VM<'a>, stack: &[Node<'a>]) -> Node<'a> {
        let mut vec = Vec::new();
        vec.push(stack[0].clone());
        let node = vm.deepseq(vec, 123);
        fail!("error: {}", node)
    }
    fn seq<'a>(vm: &'a VM<'a>, stack: &[Node<'a>]) -> Node<'a> {
        static evalCode : &'static [Instruction] = &[Eval];
        let mut temp = Vec::new();
        temp.push(stack[0].clone());
        vm.execute(&mut temp, evalCode, 123);
        stack[1].clone()
    }

}

#[cfg(test)]
mod tests {

use std::path::Path;
use std::io::File;
use typecheck::TypeEnvironment;
use compiler::{compile_with_type_env};
use vm::{VM, compile_file, execute_main, extract_result, IntResult, DoubleResult, ConstructorResult};

#[test]
fn test_primitive()
{
    assert_eq!(execute_main("main = primIntAdd 10 5".chars()), Some(IntResult(15)));
    assert_eq!(execute_main("main = primIntSubtract 7 (primIntMultiply 2 3)".chars()), Some(IntResult(1)));
    assert_eq!(execute_main("main = primIntDivide 10 (primIntRemainder 6 4)".chars()), Some(IntResult(5)));
    assert_eq!(execute_main("main = primDoubleDivide 3. 2.".chars()), Some(DoubleResult(1.5)));
    let s = 
r"data Bool = True | False
main = primIntLT 1 2";
    assert_eq!(execute_main(s.chars()), Some(ConstructorResult(0, Vec::new())));
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
fn test_nested_case() {
    let module = 
r"mult2 x = primIntMultiply x 2

main = case [mult2 123, 0] of
    : 246 xs -> primIntAdd 0 246
    [] -> 10";
    assert_eq!(execute_main(module.chars()), Some(IntResult(246)));
}

#[test]
fn test_nested_case2() {
    let module = 
r"mult2 x = primIntMultiply x 2

main = case [mult2 123, 0] of
    : 246 [] -> primIntAdd 0 246
    : x xs -> 20
    [] -> 10";
    assert_eq!(execute_main(module.chars()), Some(IntResult(20)));
}
#[test]
fn local_function() {
    let module = 
r"main =
    let
        f x y =
            let
                g x = primIntAdd x y
            in g (primIntAdd 1 x)
    in f (primIntAdd 2 0) (primIntAdd 3 0)";
    assert_eq!(execute_main(module.chars()), Some(IntResult(6)));
}

#[test]
fn test_data_types()
{
    let module = 
r"data Bool = True | False

test = False

main = case test of
    False -> primIntAdd 0 0
    True -> primIntAdd 1 0";
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


main = primIntSubtract (test (primIntAdd 5 0)) (test True)";
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

testAdd y = primIntAdd (test (primIntAdd 5 0)) (test y)

main = testAdd True";
    assert_eq!(execute_main(module.chars()), Some(IntResult(6)));
}

#[test]
fn test_run_prelude() {
    let mut type_env = TypeEnvironment::new();
    let prelude = compile_with_type_env(&mut type_env, [], File::open(&Path::new("Prelude.hs")).read_to_str().unwrap());

    let assembly = compile_with_type_env(&mut type_env, [&prelude],
r"add x y = primIntAdd x y
main = foldl add 0 [1,2,3,4]");

    let mut vm = VM::new();
    vm.add_assembly(prelude);
    vm.add_assembly(assembly);
    let x = vm.assembly.iter().flat_map(|a| a.superCombinators.iter()).find(|sc| sc.name.name == ~"main");
    let result = match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(sc.instructions, sc.assembly_id);
            extract_result(result)
        }
        None => None
    };
    assert_eq!(result, Some(IntResult(10)));
}

#[test]
fn instance_super_class() {
    let prelude = compile_file("Prelude.hs");

    let mut type_env = TypeEnvironment::new();
    let assembly = compile_with_type_env(&mut type_env, [&prelude], "main = [primIntAdd 0 1,2,3,4] == [1,2,3]");

    let mut vm = VM::new();
    vm.add_assembly(prelude);
    vm.add_assembly(assembly);
    let x = vm.assembly.iter().flat_map(|a| a.superCombinators.iter()).find(|sc| sc.name.name == ~"main");
    let result = match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(sc.instructions, sc.assembly_id);
            extract_result(result)
        }
        None => None
    };
    assert_eq!(result, Some(ConstructorResult(1, Vec::new())));
}

}
