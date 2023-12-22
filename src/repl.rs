use std::io::BufRead;

use crate::{
    compiler::*,
    core::{
        translate::*,
        Module,
        Qualified,
        Type,
    },
    interner::*,
    lambda_lift::*,
    parser::Parser,
    renamer::{
        rename_expr,
        Name,
    },
    typecheck::*,
    vm::*,
};

///Returns whether the type in question is an IO action
fn is_io(typ: &Type<Name>) -> bool {
    match *typ {
        Type::Application(ref lhs, _) => match **lhs {
            Type::Constructor(ref op) => op.name.as_ref() == "IO",
            _ => false,
        },
        _ => false,
    }
}

///Compiles an expression into an assembly
fn compile_expr(prelude: &Assembly, expr_str: &str) -> Result<Assembly, VMError> {
    let mut parser = Parser::new(expr_str.chars());
    let expr = parser.expression_().unwrap();
    let mut expr = rename_expr(expr).unwrap();

    let mut type_env = TypeEnvironment::new();
    type_env.add_types(prelude as &dyn DataTypes);
    type_env.typecheck_expr(&mut expr).unwrap();
    let temp_module = Module::from_expr(translate_expr(expr));
    let m = do_lambda_lift(temp_module);

    let mut compiler = Compiler::new();
    compiler.assemblies.push(prelude);
    Ok(compiler.compile_module(&m))
}

///Finds the main function and if it is an IO function, adds instructions to push the "RealWorld" argument
fn find_main(assembly: &Assembly) -> (Vec<Instruction>, Qualified<Type<Name>, Name>) {
    assembly
        .super_combinators
        .iter()
        .find(|sc| {
            sc.name
                == Name {
                    name: intern("main"),
                    uid: 0,
                }
        })
        .map(|sc| {
            if is_io(&sc.typ.value) {
                //If the expression we compiled is IO we need to add an extra argument
                //'RealWorld' which can be any dumb value (42 here), len - 3 is used because
                //it is currently 3 instructions Eval, Update(0), Unwind at the end of each instruction list
                //to finish the expression
                let mut vec: Vec<Instruction> = sc.instructions.iter().map(|x| x.clone()).collect();
                let len = vec.len();
                vec.insert(len - 3, Instruction::Mkap);
                vec.insert(0, Instruction::PushInt(42)); //Realworld
                (vec, sc.typ.clone())
            } else {
                (sc.instructions.clone(), sc.typ.clone())
            }
        })
        .expect("Expected main function")
}

pub fn run_and_print_expr(expr_str: &str) {
    let prelude = compile_file("Prelude.hs").unwrap();
    let mut vm = VM::new();
    vm.add_assembly(prelude);
    let assembly = compile_expr(vm.get_assembly(0), expr_str.as_ref()).unwrap();
    let (instructions, type_decl) = find_main(&assembly);
    let assembly_index = vm.add_assembly(assembly);
    let result = vm.evaluate(&*instructions, assembly_index); //TODO 0 is not necessarily correct
    println!("{:?}  {}", result, type_decl);
}

///Starts the REPL
pub fn start() {
    let mut vm = VM::new();
    match compile_file("Prelude.hs") {
        Ok(prelude) => {
            vm.add_assembly(prelude);
        }
        Err(err) => println!("Failed to compile the prelude\nReason: {}", err),
    }

    let stdin = ::std::io::stdin();
    for line in stdin.lock().lines() {
        let expr_str = match line {
            Ok(l) => l,
            Err(e) => panic!("Reading line failed with '{:?}'", e),
        };
        let assembly = match compile_expr(vm.get_assembly(0), expr_str.as_ref()) {
            Ok(assembly) => assembly,
            Err(err) => {
                println!("{}", err);
                continue;
            }
        };
        let (instructions, typ) = find_main(&assembly);
        let assembly_index = vm.add_assembly(assembly);
        let result = vm.evaluate(&*instructions, assembly_index); //TODO 0 is not necessarily correct
        println!("{:?}  {}", result, typ);
    }
}
