#[crate_id = "vm#0.0"];
#[crate_type = "bin"];
#[feature(globs)];
extern mod extra;
use std::hashmap::HashMap;
use std::io::File;
use std::str::from_utf8;
use parser::Parser;
use compiler::Compiler;
use typecheck::TypeEnvironment;
use vm::{VM, execute_main};

mod compiler;
mod typecheck;
mod lexer;
mod parser;
mod module;
mod graph;
mod vm;

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

fn main() {
    match std::os::args() {
        [_, expr_str] => {
            let mut parser = Parser::new(expr_str.chars());
            let mut expr = parser.expression_();

            let mut type_env = TypeEnvironment::new();
            type_env.typecheck(&mut expr);
            
            let mut compiler = Compiler::new(&type_env);
            let instr = compiler.compileExpression(&expr);

            let vm = VM::new();
            let result = vm.evaluate(instr);
            println!("{}", result);
        }
        [_, ~"-l", filename] => {
            let path = &Path::new(filename);
            let s  = File::open(path).read_to_end();
            let contents : &str = from_utf8(s);
            let result = execute_main(contents.chars());
            match result {
                Some(x) => println!("{:?}", x),
                None => println!("Error running file {:?}", path)
            }
        }
        _ => return println!("Expected one argument which is the expression or 2 arguments where the first is -l and the second the file to run (needs a main function)")
    }
}

