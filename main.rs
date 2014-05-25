#![crate_id = "vm#0.0"]
#![crate_type = "bin"]
#![feature(globs, phase, default_type_params, macro_rules)]
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
use vm::{VM, evaluate, execute_main, compile_file};
#[cfg(not(test))]
use core::{Module};
#[cfg(not(test))]
use core::translate::{translate_expr};
#[cfg(not(test))]
use lambda_lift::do_lambda_lift;
#[cfg(not(test))]
use renamer::{rename_expr, Name};
#[cfg(not(test))]
use interner::intern;
#[cfg(not(test))]
use std::vec::FromVec;

#[macro_escape]
macro_rules! write_core_expr(
    ($e:expr, $f:expr, $($p:pat),*) => ({
        match $e {
            Identifier(ref s) => write!($f, "{}", *s),
            Apply(ref func, ref arg) => write!($f, "({} {})", func, *arg),
            Literal(ref l) => write!($f, "{}", *l),
            Lambda(ref arg, ref body) => write!($f, "({} -> {})", *arg, *body),
            Let(ref bindings, ref body) => {
                try!(write!($f, "let \\{\n"));
                for bind in bindings.iter() {
                    try!(write!($f, "; {} = {}\n", bind.name, bind.expression));
                }
                write!($f, "\\} in {}\n", *body)
            }
            Case(ref expr, ref alts) => {
                try!(write!($f, "case {} of \\{\n", *expr));
                for alt in alts.iter() {
                    try!(write!($f, "; {} -> {}\n", alt.pattern, alt.expression));
                }
                write!($f, "\\}\n")
            }
            $($p => Ok(()))*
        }
    })
)

mod module;
mod compiler;
mod typecheck;
mod lexer;
mod parser;
mod graph;
mod vm;
mod scoped_map;
mod core;
mod lambda_lift;
mod renamer;
mod primitive;
mod interner;

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
        let expr_str = args.get(1).as_slice();
        let prelude = compile_file("Prelude.hs");
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
        let (instructions, type_decl) = assembly.superCombinators.iter()
            .find(|sc| sc.name == Name { name: intern("main"), uid: 0 })
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
                    (FromVec::from_vec(vec), sc.type_declaration.clone())
                }
                else {
                    (sc.instructions.clone(), sc.type_declaration.clone())
                }
            })
            .expect("Expected main function");
        let assembly_index = vm.add_assembly(assembly);
        let result = evaluate(&vm, instructions, assembly_index);//TODO 0 is not necessarily correct
        println!("{}  {}", result, type_decl);
    }
    else if args.len() == 3 && "-l" == args.get(1).as_slice() {
        let filename = args.get(2).as_slice();
        let path = &Path::new(filename);
        let contents = File::open(path).read_to_str().unwrap();
        let result = execute_main(contents.as_slice().chars());
        match result {
            Some(x) => println!("{:?}", x),
            None => println!("Error running file {:?}", path)
        }
    }
    else {
        println!("Expected one argument which is the expression or 2 arguments where the first is -l and the second the file to run (needs a main function)")
    }
}

