#![crate_id = "vm#0.0"]
#![crate_type = "bin"]
#![feature(globs, phase, default_type_params)]
#[phase(syntax, link)]
extern crate log;
extern crate collections;

#[cfg(not(test))]
use std::io::File;
#[cfg(not(test))]
use parser::Parser;
#[cfg(not(test))]
use compiler::Compiler;
#[cfg(not(test))]
use typecheck::{Types, TypeEnvironment};
#[cfg(not(test))]
use vm::{VM, execute_main, compile_file};

mod compiler;
mod typecheck;
mod lexer;
mod parser;
mod module;
mod graph;
mod vm;
mod scoped_map;
mod core;mod lambda_lift;

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

