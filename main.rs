#![crate_id = "vm#0.0"]
#![crate_type = "bin"]
#![feature(globs, phase, default_type_params)]
#[phase(syntax, link)]
extern crate log;
extern crate collections;
#[cfg(test)]
extern crate test;

#[cfg(not(test))]
use std::io::File;
#[cfg(not(test))]
use module::{Type, TypeApplication, TypeOperator};
#[cfg(not(test))]
use parser::Parser;
#[cfg(not(test))]
use compiler::{Compiler, Instruction, PushInt, Mkap, Eval, Split};
#[cfg(not(test))]
use typecheck::{DataTypes, TypeEnvironment};
#[cfg(not(test))]
use vm::{VM, execute_main, compile_file};
#[cfg(not(test))]
use core::{Module};
#[cfg(not(test))]
use core::translate::{translate_expr};
#[cfg(not(test))]
use lambda_lift::do_lambda_lift;
#[cfg(not(test))]
use renamer::{rename_expr, Name};

mod compiler;
mod typecheck;
mod lexer;
mod parser;
mod module;
mod graph;
mod vm;
mod scoped_map;
mod core;
mod lambda_lift;
mod renamer;
mod primitive;

#[cfg(not(test))]
fn is_io(typ: &Type) -> bool {
    match *typ {
        TypeApplication(ref lhs, _) => 
            match **lhs {
                TypeOperator(ref op) => op.name.as_slice() == "IO",
                _ => false
            },
        _ => false
    }
}

#[cfg(not(test))]
fn main() {
    let args = std::os::args();
    if args.len() == 2 {
        let expr_str = args[1];
        let prelude = compile_file(&"Prelude.hs");
        let assembly = {
            let mut parser = Parser::new(expr_str.chars());
            let mut expr = rename_expr(parser.expression_());

            let mut type_env = TypeEnvironment::new();
            type_env.add_types(&prelude as &DataTypes);
            type_env.typecheck_expr(&mut expr);
            let temp_module = Module::from_expr(translate_expr(expr));
            let m = do_lambda_lift(temp_module);
            
            let mut compiler = Compiler::new(&type_env);
            compiler.assemblies.push(&prelude);
            compiler.compileModule(&m)
        };
        let mut vm = VM::new();
        vm.add_assembly(prelude);
        let instructions = assembly.superCombinators.iter()
            .find(|sc| sc.name == Name { name: "main".to_owned(), uid: 0 })
            .map(|sc| {
                if is_io(&sc.type_declaration.typ) {
                    //If the expression we compiled is IO we need to add an extra argument
                    //'RealWorld' which can be any dumb value (42 here), len - 3 is used because
                    //it is currently 3 instructions Eval, Update(0), Unwind at the end of each instruction list
                    //to finish the expression
                    let mut vec: Vec<Instruction> = sc.instructions.iter().map(|x| x.clone()).collect();
                    let len = vec.len();
                    vec.insert(len - 3, Mkap);
                    vec.insert(0, PushInt(42));//Realworld
                    vec.move_iter().collect()
                }
                else {
                    sc.instructions.clone()
                }
            })
            .expect("Expected main function");
        let assembly_index = vm.add_assembly(assembly);
        let result = vm.evaluate(instructions, assembly_index);//TODO 0 is not necessarily correct
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

