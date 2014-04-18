#![crate_id = "vm#0.0"]
#![crate_type = "bin"]
#![feature(globs, phase, default_type_params)]
#[phase(syntax, link)]
extern crate log;
extern crate collections;
use collections::HashMap;
use std::io::File;
use std::str::from_utf8;
use parser::Parser;
use compiler::Compiler;
use typecheck::{Types, TypeEnvironment};
use vm::{VM, execute_main, compile_file};

mod compiler;
mod typecheck;
mod lexer;
mod parser;
mod module;
mod graph;
mod vm;
mod scoped_map;

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

#[cfg(not(test))]
fn main() {
    let args = std::os::args();
    if args.len() == 2 {
        let expr_str = args[1];
        let mut prelude = compile_file(&"Prelude.hs");
        let (instr, dict) = {
            let mut parser = Parser::new(expr_str.chars());
            let mut expr = parser.expression_();

            let mut type_env = TypeEnvironment::new();
            type_env.add_types(&prelude as &Types);
            type_env.typecheck_expr(&mut expr);
            
            let mut compiler = Compiler::new(&type_env);
            compiler.assemblies.push(&prelude);
            let i = compiler.compileExpression(&expr);
            (i, compiler.instance_dictionaries.get(0).map(|&(_, ref x)| x.clone()))
        };
        //Add the dictionary if one is needed
        match dict {
            Some(dict) => prelude.instance_dictionaries.push(dict),
            None => ()
        };
        let mut vm = VM::new();
        vm.add_assembly(prelude);
        let result = vm.evaluate(instr, 0);//TODO 0 is not necessarily correct
        println!("{}", result);
    }
    else if args.len() == 3 && "-l" == args[1] {
        let filename = args[2];
        let path = &Path::new(filename);
        let contents = File::open(path).read_to_str().unwrap();
        let result = execute_main(contents.chars());
        match result {
            Some(x) => println!("{:?}", x),
            None => println!("Error running file {:?}", path)
        }
    }
    else {
        println!("Expected one argument which is the expression or 2 arguments where the first is -l and the second the file to run (needs a main function)")
    }
}

