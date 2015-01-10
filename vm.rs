use std::fmt;
use std::rc::Rc;
use std::cell::{Ref, RefMut, RefCell};
use std::path::Path;
use std::io::{File, IoResult};
use typecheck::TypeEnvironment;
use compiler::*;
use parser::Parser;
use core::translate::translate_module;
use lambda_lift::do_lambda_lift;
use renamer::rename_module;
use vm::primitive::{BuiltinFun, get_builtin};
use interner::*;

use self::Node_::*;

#[derive(Clone)]
struct InstanceDictionary {
    entries: Vec<Rc<DictionaryEntry>>
}
#[derive(Clone)]
enum DictionaryEntry {
    Function(usize),
    App(usize, InstanceDictionary)
}

enum Node_<'a> {
    Application(Node<'a>, Node<'a>),
    Int(isize),
    Float(f64),
    Char(char),
    Combinator(&'a SuperCombinator),
    Indirection(Node<'a>),
    Constructor(u16, Vec<Node<'a>>),
    Dictionary(InstanceDictionary),
    BuiltinFunction(usize, BuiltinFun)
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
            &Dictionary(ref dict) => Dictionary(dict.clone()),
            &BuiltinFunction(arity, f) => BuiltinFunction(arity, f)
        }
    }
}

#[derive(Clone)]
struct Node<'a> {
    node: Rc<RefCell<Node_<'a>>>
}

impl <'a> Node<'a> {
    ///Creates a new node
    fn new(n : Node_<'a>) -> Node<'a> {
        Node { node: Rc::new(RefCell::new(n)) }
    }
    fn borrow<'b>(&'b self) -> Ref<'b, Node_<'a>> {
        (*self.node).borrow()
    }
    fn borrow_mut<'b>(&'b self) -> RefMut<'b, Node_<'a>> {
        (*self.node).borrow_mut()
    }
}
impl <'a> fmt::Show for Node<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", *self.borrow())
    }
}
impl <'a> fmt::Show for Node_<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Application(ref func, ref arg) => write!(f, "({:?} {:?})", *func, *arg),
            &Int(i) => write!(f, "{:?}", i),
            &Float(i) => write!(f, "{:?}f", i),
            &Char(c) => write!(f, "'{:?}'", c),
            &Combinator(ref sc) => write!(f, "{:?}", sc.name),
            &Indirection(ref n) => write!(f, "(~> {:?})", *n),
            &Constructor(ref tag, ref args) => {
                let cons = args;
                if cons.len() > 0 {
                    match *cons[0].borrow() {
                        Char(_) => {
                            fn print_string<'a>(f: &mut fmt::Formatter, cons: &Vec<Node<'a>>) -> fmt::Result {
                                if cons.len() >= 2 {
                                    match *cons[0].borrow() {
                                        Char(c) =>  { try!(write!(f, "{:?}", c)); },
                                        _ => ()
                                    }
                                    match *cons[1].borrow() {
                                        Constructor(_, ref args2) => return print_string(f, args2),
                                        _ => ()
                                    }
                                }
                                Ok(())
                            }
                            try!(write!(f, "\""));
                            try!(print_string(f, cons));
                            write!(f, "\"")
                        }
                        _ => {
                            //Print a normal constructor
                            try!(write!(f, "{{{:?}", *tag));
                            for arg in args.iter() {
                                try!(write!(f, " {:?}", *arg.borrow()));
                            }
                            write!(f, "}}")
                        }
                    }
                }
                else {
                    //Print a normal constructor
                    try!(write!(f, "{{{:?}", *tag));
                    for arg in args.iter() {
                        try!(write!(f, " {:?}", *arg.borrow()));
                    }
                    write!(f, "}}")
                }
            }
            &Dictionary(ref dict) => write!(f, "{:?}", dict),
            &BuiltinFunction(..) => write!(f, "<extern function>")
        }
    }
}
impl fmt::Show for InstanceDictionary {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "["));
        if self.entries.len() > 0 {
            try!(write!(f, "{:?}", *self.entries[0]));
        }
        for entry in self.entries.iter().skip(1) {
            try!(write!(f, ", {:?}", **entry));
        }
        write!(f, "]")
    }
}
impl fmt::Show for DictionaryEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DictionaryEntry::Function(index) => write!(f, "{:?}", index),
            DictionaryEntry::App(ref func, ref arg) => write!(f, "({:?} {:?})", *func, *arg)
        }
    }
}

pub struct VM {
    ///Vector of all assemblies which are loaded.
    assembly : Vec<Assembly>,
    ///A pair of (assembly_index, function_index).
    globals: Vec<(usize, usize)>,
}

impl <'a> VM {
    pub fn new() -> VM {
        VM { assembly : Vec::new(), globals: Vec::new() }
    }

    ///Adds an assembly to the VM, adding entries to the global table as necessary
    pub fn add_assembly(&mut self, assembly: Assembly) -> usize {
        self.assembly.push(assembly);
        let assembly_index = self.assembly.len() - 1;
        for index in range(0, self.assembly.last().unwrap().superCombinators.len()) {
            self.globals.push((assembly_index, index));
        }
        assembly_index
    }
    ///Returns a reference to the assembly at the index
    pub fn get_assembly(&self, index: usize) -> &Assembly {
        &self.assembly[index]
    }

    ///Evaluates the code into Head Normal Form (HNF)
    pub fn evaluate(&self, code: &[Instruction], assembly_id: usize) -> Node_ {
        let mut stack = Vec::new();
        self.execute(&mut stack, code, assembly_id);
        self.deepseq(stack, assembly_id)
    }
    
    ///Evaluates the what is at the top of the stack into HNF
    fn deepseq(&'a self, mut stack: Vec<Node<'a>>, assembly_id: usize) -> Node_<'a> {
        static EVALCODE : &'static [Instruction] = &[Instruction::Eval];
        self.execute(&mut stack, EVALCODE, assembly_id);
        match *stack[0].borrow() {
            Constructor(tag, ref vals) => {
                let mut ret = Vec::new();
                for v in vals.iter() {
                    let s = vec!(v.clone());
                    let x = self.deepseq(s, assembly_id);
                    ret.push(Node::new(x));
                }
                Constructor(tag, ret)
            }
            _ => stack[0].borrow().clone()
        }
    }

    ///Executes a sequence of instructions, leaving the result on the top of the stack
    pub fn execute(&'a self, stack: &mut Vec<Node<'a>>, code: &[Instruction], assembly_id: usize) {
        use compiler::Instruction::*;
        debug!("----------------------------");
        debug!("Entering frame with stack");
        for x in stack.iter() {
            debug!("{:?}", *x.borrow());
        }
        debug!("");
        let mut i = 0;
        while i < code.len() {
            debug!("Executing instruction {:?} : {:?}", i, code[i]);
            match code[i] {
                Add => primitive(stack, |l, r| { l + r }),
                Sub => primitive(stack, |l, r| { l - r }),
                Multiply => primitive(stack, |l, r| { l * r }),
                Divide => primitive(stack, |l, r| { l / r }),
                Remainder => primitive(stack, |l, r| { l % r }),
                IntEQ => primitive_int(stack, |l, r| { if l == r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                IntLT => primitive_int(stack, |l, r| { if l < r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                IntLE => primitive_int(stack, |l, r| { if l <= r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                IntGT => primitive_int(stack, |l, r| { if l > r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                IntGE => primitive_int(stack, |l, r| { if l >= r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                DoubleAdd => primitive_float(stack, |l, r| { Float(l + r) }),
                DoubleSub => primitive_float(stack, |l, r| { Float(l - r) }),
                DoubleMultiply => primitive_float(stack, |l, r| { Float(l * r) }),
                DoubleDivide => primitive_float(stack, |l, r| { Float(l / r) }),
                DoubleRemainder => primitive_float(stack, |l, r| { Float(l % r) }),
                DoubleEQ => primitive_float(stack, |l, r| { if l == r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                DoubleLT => primitive_float(stack, |l, r| { if l < r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                DoubleLE => primitive_float(stack, |l, r| { if l <= r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                DoubleGT => primitive_float(stack, |l, r| { if l > r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                DoubleGE => primitive_float(stack, |l, r| { if l >= r { Constructor(0, Vec::new()) } else { Constructor(1, Vec::new()) } }),
                IntToDouble => {
                    let top = stack.pop().unwrap();
                    stack.push(match *top.borrow() {
                        Int(i) => Node::new(Float(i as f64)),
                        _ => panic!("Excpected Int in Int -> Double cast")
                    });
                }
                DoubleToInt => {
                    let top = stack.pop().unwrap();
                    stack.push(match *top.borrow() {
                        Float(f) => Node::new(Int(f as isize)),
                        _ => panic!("Excpected Double in Double -> Int cast")
                    });
                }
                PushInt(value) => { stack.push(Node::new(Int(value))); }
                PushFloat(value) => { stack.push(Node::new(Float(value))); }
                PushChar(value) => { stack.push(Node::new(Char(value))); }
                Push(index) => {
                    let x = stack[index].clone();
                    debug!("Pushed {:?}", *x.borrow());
                    for j in range(0, stack.len()) {
                        debug!(" {:?}  {:?}", j, *stack[j].borrow());
                    }
                    stack.push(x);
                }
                PushGlobal(index) => {
                    let (assembly_index, index) = self.globals[index];
                    let sc = &self.assembly[assembly_index].superCombinators[index];
                    stack.push(Node::new(Combinator(sc)));
                }
                PushBuiltin(index) => {
                    let (arity, f) = get_builtin(index);
                    stack.push(Node::new(BuiltinFunction(arity, f)));
                }
                Mkap => {
                    assert!(stack.len() >= 2);
                    let func = stack.pop().unwrap();
                    let arg = stack.pop().unwrap();
                    debug!("Mkap {:?} {:?}", *func.borrow(), *arg.borrow());
                    stack.push(Node::new(Application(func, arg)));
                }
                Eval => {
                    static UNWINDCODE : &'static [Instruction] = &[Unwind];
                    let old = stack.pop().unwrap();
                    let mut newStack = vec!(old.clone());
                    self.execute(&mut newStack, UNWINDCODE, assembly_id);
                    stack.push(newStack.pop().unwrap());
                    debug!("{:?}", stack.as_slice());
                    let new = stack.last().unwrap().borrow().clone();
                    *(*old.node).borrow_mut() = new;
                    debug!("{:?}", stack.as_slice());
                }
                Pop(num) => {
                    for _ in range(0, num) {
                        stack.pop();
                    }
                }
                Update(index) => {
                    stack[index] = Node::new(Indirection(stack.last().unwrap().clone()));
                }
                Unwind => {
                    fn unwind<'a, F>(i_ptr: &mut usize, arity: usize, stack: &mut Vec<Node<'a>>, f: F)
                        where F: FnOnce(&mut Vec<Node<'a>>) -> Node<'a> {
                        if stack.len() - 1 < arity {
                            while stack.len() > 1 {
                                stack.pop();
                            }
                        }
                        else {
                            for j in range(stack.len() - arity - 1, stack.len() - 1) {
                                stack[j] = match *stack[j].borrow() {
                                    Application(_, ref arg) => arg.clone(),
                                    _ => panic!("Expected Application")
                                };
                            }
                            let value = {
                                let mut new_stack = Vec::new();
                                for i in range(0, arity) {
                                    let index = stack.len() - i - 2;
                                    new_stack.push(stack[index].clone());
                                }
                                f(&mut new_stack)
                            };
                            for _ in range(0, arity + 1) {
                                stack.pop();
                            }
                            stack.push(value);
                            *i_ptr -= 1;
                        }
                    }
                    let x = (*stack.last().unwrap().borrow()).clone();
                    debug!("Unwinding {:?}", x);
                    match x {
                        Application(func, _) => {
                            stack.push(func);
                            i -= 1;//Redo the unwind instruction
                        }
                        Combinator(comb) => {
                            debug!(">>> Call {:?}", comb.name);
                            unwind(&mut i, comb.arity, stack, |new_stack| {
                                self.execute(new_stack, &*comb.instructions, comb.assembly_id);
                                new_stack.pop().unwrap()
                            });
                        }
                        BuiltinFunction(arity, func) => {
                            unwind(&mut i, arity, stack, |new_stack| func(self, new_stack.as_slice()));
                        }
                        Indirection(node) => {
                            *stack.last_mut().unwrap() = node;
                            i -= 1;
                        }
                        _ => ()
                    }
                }
                Slide(size) => {
                    let top = stack.pop().unwrap();
                    for _ in range(0, size) {
                        stack.pop();
                    }
                    stack.push(top);
                }
                Split(_) => {
                    match *stack.pop().unwrap().borrow() {
                        Constructor(_, ref fields) => {
                            for field in fields.iter() {
                                stack.push(field.clone());
                            }
                        }
                        _ => panic!("Expected constructor in Split instruction")
                    }
                }
                Pack(tag, arity) => {
                    let mut args = Vec::new();
                    for _ in range(0, arity) {
                        args.push(stack.pop().unwrap());
                    }
                    stack.push(Node::new(Constructor(tag, args)));
                }
                JumpFalse(address) => {
                    match *stack.last().unwrap().borrow() {
                        Constructor(0, _) => (),
                        Constructor(1, _) => i = address - 1,
                        _ => ()
                    }
                    stack.pop();
                }
                CaseJump(jump_tag) => {
                    let jumped = match *stack.last().unwrap().borrow() {
                        Constructor(tag, _) => {
                            if jump_tag == tag as usize {
                                i += 1;//Skip the jump instruction ie continue to the next test
                                true
                            }
                            else {
                                false
                            }
                        }
                        ref x => panic!("Expected constructor when executing CaseJump, got {:?}", *x),
                    };
                    if !jumped {
                        stack.pop();
                    }
                }
                Jump(to) => {
                    i = to - 1;
                }
                PushDictionary(index) => {
                    let assembly = &self.assembly[assembly_id];
                    let dict : &[usize] = &*assembly.instance_dictionaries[index];
                    let dict = InstanceDictionary { entries: dict.iter().map(|i| Rc::new(DictionaryEntry::Function(*i))).collect() };
                    stack.push(Node::new(Dictionary(dict)));
                }
                PushDictionaryMember(index) => {
                    let sc = {
                        let x = stack[0].borrow();
                        let dict = match *x {
                            Dictionary(ref x) => x,
                            ref x => panic!("Attempted to retrieve {:?} as dictionary", *x)
                        };
                        match *dict.entries[index] {
                            DictionaryEntry::Function(gi) => {
                                let (assembly_index, i) = self.globals[gi];
                                Combinator(&self.assembly[assembly_index].superCombinators[i])
                            }
                            DictionaryEntry::App(gi, ref dict) => {
                                let (assembly_index, i) = self.globals[gi];
                                let sc = &self.assembly[assembly_index].superCombinators[i];
                                Application(Node::new(Combinator(sc)), Node::new(Dictionary(dict.clone())))
                            }
                        }
                    };
                    stack.push(Node::new(sc));
                }
                MkapDictionary => {
                    let a = stack.pop().unwrap();
                    let a = a.borrow();
                    let arg = match *a {
                        Dictionary(ref d) => {
                            d
                        }
                        _ => panic!()
                    };
                    let func = stack.pop().unwrap();
                    let mut new_dict = InstanceDictionary { entries: Vec::new() };
                    match *func.borrow() {
                        Dictionary(ref d) => {
                            for entry in d.entries.iter() {
                                match **entry {
                                    DictionaryEntry::Function(index) => {
                                        new_dict.entries.push(Rc::new(DictionaryEntry::App(index, arg.clone())));
                                    }
                                    _ => panic!()
                                }
                            }
                        }
                        _ => panic!()
                    }
                    stack.push(Node::new(Dictionary(new_dict)));
                }
                ConstructDictionary(size) => {
                    let mut new_dict = InstanceDictionary { entries: Vec::new() };
                    for _ in range(0, size) {
                        match *stack.pop().unwrap().borrow() {
                            Dictionary(ref d) => {
                                new_dict.entries.extend(d.entries.iter().map(|x| x.clone()));
                            }
                            ref x => panic!("Unexpected {:?}", x)
                        }
                    }
                    stack.push(Node::new(Dictionary(new_dict)));
                }
                PushDictionaryRange(start, size) => {
                    let mut new_dict = InstanceDictionary { entries: Vec::new() };
                    match *stack[0].borrow() {
                        Dictionary(ref d) => {
                            new_dict.entries.extend(d.entries.iter().skip(start).take(size).map(|x| x.clone()));
                        }
                        _ => panic!()
                    }
                    stack.push(Node::new(Dictionary(new_dict)));
                }
            }
            i += 1;
        }
        debug!("End frame");
        debug!("--------------------------");
    }
}


///Exucutes a binary primitive instruction taking two integers
fn primitive_int<'a, F>(stack: &mut Vec<Node<'a>>, f: F) where F: FnOnce(isize, isize) -> Node_<'a> {
    let l = stack.pop().unwrap();
    let r = stack.pop().unwrap();
    match (&*l.borrow(), &*r.borrow()) {
        (&Int(lhs), &Int(rhs)) => stack.push(Node::new(f(lhs, rhs))),
        (lhs, rhs) => panic!("Expected fully evaluted numbers in primitive instruction\n LHS: {:?}\nRHS: {:?} ", lhs, rhs)
    }
}
///Exucutes a binary primitive instruction taking two doubles
fn primitive_float<'a, F>(stack: &mut Vec<Node<'a>>, f: F) where F: FnOnce(f64, f64) -> Node_<'a> {
    let l = stack.pop().unwrap();
    let r = stack.pop().unwrap();
    match (&*l.borrow(), &*r.borrow()) {
        (&Float(lhs), &Float(rhs)) => stack.push(Node::new(f(lhs, rhs))),
        (lhs, rhs) => panic!("Expected fully evaluted numbers in primitive instruction\n LHS: {:?}\nRHS: {:?} ", lhs, rhs)
    }
}
fn primitive<F>(stack: &mut Vec<Node>, f: F) where F: FnOnce(isize, isize) -> isize {
    primitive_int(stack, move |l, r| Int(f(l, r)))
}

#[derive(PartialEq, Show)]
enum VMResult {
    Int(isize),
    Double(f64),
    Constructor(u16, Vec<VMResult>)
}

fn compile_iter<T : Iterator<Item=char>>(iterator: T) -> Assembly {
    let mut parser = Parser::new(iterator);
    let mut module = rename_module(parser.module());
    
    let mut typer = TypeEnvironment::new();
    typer.typecheck_module(&mut module);
    let core_module = do_lambda_lift(translate_module(module));
    
    let mut compiler = Compiler::new();
    compiler.compile_module(&core_module)
}

///Compiles a single file
pub fn compile_file(filename: &str) -> Assembly {
    let path = &Path::new(filename);
    let contents = File::open(path).read_to_string().unwrap();
    compile_iter(contents.as_slice().chars())
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
            Some(VMResult::Constructor(tag, result))
        }
        Int(i) => Some(VMResult::Int(i)),
        Float(i) => Some(VMResult::Double(i)),
        x => {
            println!("Can't extract result {:?}", x);
            None
        }
    }
}

pub fn execute_main_string(module: &str) -> IoResult<Option<VMResult>> {
    let assemblies = try!(compile_string(module));
    execute_main_module_(assemblies)
}

///Takes a module with a main function and compiles it and all its imported modules
///and then executes the main function
pub fn execute_main_module(modulename: &str) -> IoResult<Option<VMResult>> {
    let assemblies = try!(compile_module(modulename));
    execute_main_module_(assemblies)
}

fn execute_main_module_(assemblies: Vec<Assembly>) -> IoResult<Option<VMResult>> {
    let mut vm = VM::new();
    for assembly in assemblies.into_iter() {
        vm.add_assembly(assembly);
    }
    let x = vm.assembly.iter().flat_map(|a| a.superCombinators.iter()).find(|sc| sc.name.name == intern("main"));
    match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(&*sc.instructions, sc.assembly_id);
            Ok(extract_result(result))
        }
        None => Ok(None)
    }
}

//We mirror the naming scheme from Haskell here which is camelCase
#[allow(non_snake_case_functions)]
mod primitive {

    use std::io::fs::File;
    use vm::{VM, Node, Node_};
    use vm::Node_::{Application, Constructor, BuiltinFunction, Char};
    use compiler::Instruction;
    use compiler::Instruction::Eval;

    pub fn get_builtin(i: usize) -> (usize, BuiltinFun) {
        match i {
            0 => (1, error),
            1 => (2, seq),
            2 => (2, readFile),
            3 => (3, io_bind),
            4 => (2, io_return),
            5 => (2, putStrLn),
            6 => (2, compare_tags),
            _ => panic!("undefined primitive")
        }
    }

    pub type BuiltinFun = for <'a> extern "Rust" fn (&'a VM, &[Node<'a>]) -> Node<'a>;

    fn error<'a>(vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        let mut vec = Vec::new();
        vec.push(stack[0].clone());
        let node = vm.deepseq(vec, 123);
        panic!("error: {:?}", node)
    }
    fn eval<'a>(vm: &'a VM, node: Node<'a>) -> Node<'a> {
        static EVALCODE : &'static [Instruction] = &[Eval];
        let mut temp = Vec::new();
        temp.push(node);
        vm.execute(&mut temp, EVALCODE, 123);
        temp.pop().unwrap()
    }
    fn seq<'a>(vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        eval(vm, stack[0].clone());
        stack[1].clone()
    }
    fn io_bind<'a>(_vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        //IO a -> (a -> IO b) -> IO b
        //IO a = (RealWorld -> (a, RealWorld)
        //((RealWorld -> (a, RealWorld)) -> (a -> RealWorld -> (b, RealWorld)) -> RealWorld -> (b, RealWorld)
        //             0                                      1                        2 
        //(a, RealWorld)
        let aw = Node::new(Application(stack[0].clone(), stack[2].clone()));
        let p = Node::new(BuiltinFunction(2, pass));
        Node::new(Application(Node::new(Application(p, aw)), stack[1].clone()))
    }
    fn pass<'a>(vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        //(a, RealWorld) -> (a -> RealWorld -> (b, RealWorld)) -> (b, RealWorld)
        eval(vm, stack[0].clone());
        let aw = stack[0].borrow();
        let (a, rw) = match *aw {
            Constructor(_, ref args) => (&args[0], &args[1]),
            _ => panic!("pass exepected constructor")
        };
        Node::new(Application(Node::new(Application(stack[1].clone(), a.clone())), rw.clone()))
    }
    fn io_return<'a>(_vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        //a -> RealWorld -> (a, RealWorld)
        Node::new(Constructor(0, vec!(stack[0].clone(), stack[1].clone())))
    }
    fn readFile<'a>(vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        let mut temp = Vec::new();
        temp.push(stack[0].clone());
        let node_filename = vm.deepseq(temp, 123);
        let filename = get_string(&node_filename);
        let mut file = match File::open(&Path::new(filename.as_slice())) {
            Ok(f) => f,
            Err(err) => panic!("error: readFile -> {:?}", err)
        };
        let (begin, _end) = match file.read_to_string() {
            Ok(s) => create_string(s.as_slice()),
            Err(err) => panic!("error: readFile -> {:?}", err)
        };
        //Return (String, RealWorld)
        Node::new(Constructor(0, vec!(begin, stack[1].clone())))
    }

    fn putStrLn<'a>(vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        let mut temp = Vec::new();
        temp.push(stack[0].clone());
        let msg_node = vm.deepseq(temp, 123);
        let msg = get_string(&msg_node);
        println!("{:?}", msg);
        Node::new(Constructor(0, vec!(Node::new(Constructor(0, vec!())), stack[1].clone())))
    }
    fn get_string<'a>(node: &Node_<'a>) -> String {
        fn get_string_<'a>(buffer: &mut String, node: &Node_<'a>) {
            match *node {
                Constructor(_, ref args) => {
                    if args.len() == 2 {
                        match *args[0].borrow() {
                            Char(c) => buffer.push(c),
                            _ => panic!("Unevaluated char")
                        }
                        get_string_(buffer, &*args[1].borrow());
                    }
                }
                _ => panic!("Unevaluated list")
            }
        }
        let mut buffer = String::new();
        get_string_(&mut buffer, node);
        buffer
    }
    fn create_string<'a>(s: &str) -> (Node<'a>, Node<'a>) {
        let mut node = Node::new(Constructor(0, vec!()));
        let first = node.clone();
        for c in s.chars() {
            node = match &mut *node.borrow_mut() {
                &mut Constructor(ref mut tag, ref mut args) => {
                    *tag = 1;
                    args.push(Node::new(Char(c)));
                    args.push(Node::new(Constructor(0, Vec::new())));
                    args[1].clone()
                }
                _ => panic!()
            };
        }
        (first, node)
    }
    ///Compares the tags of two constructors, returning an Ordering
    fn compare_tags<'a>(vm: &'a VM, stack: &[Node<'a>]) -> Node<'a> {
        use std::cmp::Ordering;
        assert_eq!(stack.len(), 2);
        let lhs = eval(vm, stack[0].clone());
        let rhs = eval(vm, stack[1].clone());
        let tag = match (&*lhs.borrow(), &*rhs.borrow()) {
            (&Constructor(lhs, _), &Constructor(rhs, _)) => match lhs.cmp(&rhs) {
                Ordering::Less => 0,
                Ordering::Equal => 1,
                Ordering::Greater => 2
            },
            (_, _) => 1//EQ
        };
        Node::new(Constructor(tag, Vec::new()))
    }
}

#[cfg(test)]
mod tests {

use typecheck::TypeEnvironment;
use compiler::{compile_with_type_env};
use vm::{VM, compile_file, compile_iter, execute_main_module, execute_main_string, extract_result, VMResult};
use vm::VMResult::{Int, Double, Constructor};
use interner::*;

fn execute_main<T : Iterator<Item=char>>(iterator: T) -> Option<VMResult> {
    let mut vm = VM::new();
    vm.add_assembly(compile_iter(iterator));
    let x = vm.assembly.iter().flat_map(|a| a.superCombinators.iter()).find(|sc| sc.name.name == intern("main"));
    match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(&*sc.instructions, sc.assembly_id);
            extract_result(result)
        }
        None => None
    }
}

#[test]
fn test_primitive()
{
    assert_eq!(execute_main("main = primIntAdd 10 5".chars()), Some(VMResult::Int(15)));
    assert_eq!(execute_main("main = primIntSubtract 7 (primIntMultiply 2 3)".chars()), Some(VMResult::Int(1)));
    assert_eq!(execute_main("main = primIntDivide 10 (primIntRemainder 6 4)".chars()), Some(VMResult::Int(5)));
    assert_eq!(execute_main("main = primDoubleDivide 3. 2.".chars()), Some(VMResult::Double(1.5)));
    let s = 
r"data Bool = True | False
main = primIntLT 1 2";
    assert_eq!(execute_main(s.chars()), Some(VMResult::Constructor(0, Vec::new())));
}

#[test]
fn test_function()
{
    let module = 
r"mult2 x = primIntMultiply x 2

main = mult2 10";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(20)));

    let module2 = 
r"mult2 x = primIntMultiply x 2

add x y = primIntAdd y x

main = add 3 (mult2 10)";
    assert_eq!(execute_main(module2.chars()), Some(VMResult::Int(23)));
}
#[test]
fn test_case()
{
    let module = 
r"mult2 x = primIntMultiply x 2

main = case [mult2 123, 0] of
    x:xs -> x
    [] -> 10";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(246)));
}

#[test]
fn test_nested_case() {
    let module = 
r"mult2 x = primIntMultiply x 2

main = case [mult2 123, 0] of
    246:xs -> primIntAdd 0 246
    [] -> 10";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(246)));
}

#[test]
fn test_nested_case2() {
    let module = 
r"mult2 x = primIntMultiply x 2

main = case [mult2 123, 0] of
    246:[] -> primIntAdd 0 246
    x:xs -> 20
    [] -> 10";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(20)));
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
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(6)));
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
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(0)));
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
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(4)));
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
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(6)));
}

#[test]
fn test_run_prelude() {
    let prelude = compile_file("Prelude.hs");
    let assembly = {
        let mut type_env = TypeEnvironment::new();

        compile_with_type_env(&mut type_env, &[&prelude],
r"add x y = primIntAdd x y
main = foldl add 0 [1,2,3,4]")
    };

    let mut vm = VM::new();
    vm.add_assembly(prelude);
    vm.add_assembly(assembly);
    let x = vm.assembly.iter().flat_map(|a| a.superCombinators.iter()).find(|sc| sc.name.name == intern("main"));
    let result = match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(&*sc.instructions, sc.assembly_id);
            extract_result(result)
        }
        None => None
    };
    assert_eq!(result, Some(VMResult::Int(10)));
}

#[test]
fn instance_super_class() {
    let prelude = compile_file("Prelude.hs");

    let assembly = {
        let mut type_env = TypeEnvironment::new();
        compile_with_type_env(&mut type_env, &[&prelude], "main = [primIntAdd 0 1,2,3,4] == [1,2,3]")
    };

    let mut vm = VM::new();
    vm.add_assembly(prelude);
    vm.add_assembly(assembly);
    let x = vm.assembly.iter().flat_map(|a| a.superCombinators.iter()).find(|sc| sc.name.name == intern("main"));
    let result = match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(&*sc.instructions, sc.assembly_id);
            extract_result(result)
        }
        None => None
    };
    assert_eq!(result, Some(VMResult::Constructor(1, Vec::new())));
}

#[test]
fn monad_do() {
    let prelude = compile_file("Prelude.hs");

    let assembly = {
        let mut type_env = TypeEnvironment::new();
        compile_with_type_env(&mut type_env, &[&prelude],
"
test :: Maybe Int -> Maybe Int -> Maybe Int
test x y = do
    x1 <- x
    y
    return (x1 + 1)

main = test (Just 4) (Just 6)")
    };

    let mut vm = VM::new();
    vm.add_assembly(prelude);
    vm.add_assembly(assembly);
    let x = vm.assembly.iter().flat_map(|a| a.superCombinators.iter()).find(|sc| sc.name.name == intern("main"));
    let result = match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(&*sc.instructions, sc.assembly_id);
            extract_result(result)
        }
        None => None
    };
    assert_eq!(result, Some(VMResult::Constructor(0, vec!(VMResult::Int(5)))));
}

#[test]
fn import() {
    let result = execute_main_module("Test");
    assert_eq!(result, Ok(Some(VMResult::Int(6))));
}

#[test]
fn pattern_bind() {
    let result = execute_main_string(
r"
import Prelude

test :: [Bool] -> Bool
test (True:[]) = False
test (True:y:ys) = y
test [] = False

main = test [True, True]
")
    .unwrap_or_else(|err| panic!(err));
    assert_eq!(result, Some(VMResult::Constructor(0, Vec::new())));
}
#[test]
fn pattern_guards() {
    let result = execute_main_string(
r"
import Prelude

test :: Int -> [a] -> Int
test 2 _ = 2
test x []
    | primIntLT x 0 = primIntSubtract 0 1
    | primIntGT x 0 = 1
test x _ = x

main = (test 2 [], test 100 [], test 100 ['c'])

")
    .unwrap_or_else(|err| panic!(err));
    assert_eq!(result, Some(VMResult::Constructor(0, vec!(VMResult::Int(2), VMResult::Int(1), VMResult::Int(100)))));
}

#[test]
fn pattern_guards_nested() {
    let result = execute_main_string(
r"
import Prelude

test :: Int -> [Int] -> Int
test 2 _ = 2
test x (0:[])
    | primIntLT x 0 = primIntSubtract 0 1
    | primIntGT x 0 = 1
test x _ = x

main = (test 2 [], test 100 [0], test 100 [0, 123])

")
    .unwrap_or_else(|err| panic!(err));
    assert_eq!(result, Some(VMResult::Constructor(0, vec!(VMResult::Int(2), VMResult::Int(1), VMResult::Int(100)))));
}
#[test]
fn test_class_default_function()
{
    let module = 
r"data Bool = True | False

class Test a where
    test :: a -> Int
    test _ = 42
    test2 :: Int

instance Test Int where
    test x = x
    test2 = 0

instance Test Bool where
    test2 = 2

main = (test True, test (1 :: Int))";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Constructor(0, vec![VMResult::Int(42), VMResult::Int(1)])));
}

#[test]
fn use_super_class() {
    let result = execute_main_string(
r"
import Prelude

test x y = (x == y) || (x < y)
main = (test (0 :: Int) 2) && not (test (1 :: Int) 0)")
        .unwrap_or_else(|err| panic!("{:?}", err));
    assert_eq!(result, Some(VMResult::Constructor(0, Vec::new())));
}
#[test]
fn implement_class() {
    let result = execute_main_string(
r"
import Prelude
data AB = A | B

instance Eq AB where
    (==) A A = True
    (==) B B = True
    (==) _ _ = False

test x y = x == y

main = A == B && test A A")
        .unwrap_or_else(|err| panic!("{:?}", err));
    assert_eq!(result, Some(VMResult::Constructor(1, Vec::new())));
}

#[test]
fn deriving_eq() {
    let result = execute_main_string(
r"
import Prelude
data Test = A Int | B
    deriving(Eq)

main = A 0 == A 2 || A 0 == B
").unwrap_or_else(|err| panic!(err));
    assert_eq!(result, Some(VMResult::Constructor(1, Vec::new())));
}
#[test]
fn deriving_ord() {
    let result = execute_main_string(
r"
import Prelude
data Test = A Int | B
    deriving(Eq, Ord)

main = compare (A 0) (A 2) == LT && compare B (A 123) == GT
").unwrap_or_else(|err| panic!(err));
    assert_eq!(result, Some(VMResult::Constructor(0, Vec::new())));
}

#[test]
fn instance_eq_list() {
    let result = execute_main_string(
r"
import Prelude
test x y = x == y
main = test [1 :: Int] [3]
").unwrap_or_else(|err| panic!(err));
    assert_eq!(result, Some(VMResult::Constructor(1, Vec::new())));
}
#[test]
fn build_dictionary() {
    //Test that the compiler can generate code to build a dictionary at runtime
    let result = execute_main_string(
r"
import Prelude
test :: Eq a => a -> a -> Bool
test x y = [x] == [y]
main = test [1 :: Int] [3]
").unwrap_or_else(|err| panic!(err));
    assert_eq!(result, Some(VMResult::Constructor(1, Vec::new())));
}

#[test]
fn if_else() {
    let result = execute_main_string(
r"
import Prelude

main = let
        x = 123 :: Int
    in if x < 0
        then x
        else 1
").unwrap_or_else(|err| panic!(err));
    assert_eq!(result, Some(VMResult::Int(1)));
}

#[test]
fn newtype() {
    let result = execute_main_string(
r"
import Prelude
newtype Even = Even Int

makeEven :: Int -> Maybe Even
makeEven i
    | i `div` 2 /= (i - 1) `div` 2 = Just (Even i)
    | otherwise = Nothing

main = makeEven (100 * 3)
").unwrap_or_else(|err| panic!(err));

    assert_eq!(result, Some(VMResult::Constructor(0, vec![VMResult::Int(300)])));
}

#[test]
fn where_bindings() {
    let result = execute_main_string(
r"
import Prelude

main = case list of
        [] -> 123
        x:xs
            | y < 10 -> 0
            | otherwise -> y
            where
            y = x + 10
    where
        list = [1::Int]
").unwrap_or_else(|err| panic!(err));
    assert_eq!(result, Some(VMResult::Int(11)));
}

}
