use compiler::*;
use typecheck::*;
use vm::*;
use interner::*;
use core::{Module, Type, Qualified};
use core::Type::{Application, Constructor};
use core::translate::*;
use lambda_lift::*;
use parser::Parser;
use renamer::{Name, rename_expr};

///Returns whether the type in question is an IO action
fn is_io(typ: &Type) -> bool {
    match *typ {
        Type::Application(ref lhs, _) => 
            match **lhs {
                Type::Constructor(ref op) => op.name.as_slice() == "IO",
                _ => false
            },
        _ => false
    }
}

///Compiles an expression into an assembly
fn compile_expr(prelude: &Assembly, expr_str: &str) -> Assembly {
    let mut parser = Parser::new(expr_str.chars());
    let mut expr = rename_expr(parser.expression_());

    let mut type_env = TypeEnvironment::new();
    type_env.add_types(prelude as &DataTypes);
    type_env.typecheck_expr(&mut expr);
    let temp_module = Module::from_expr(translate_expr(expr));
    let m = do_lambda_lift(temp_module);
    
    let mut compiler = Compiler::new();
    compiler.assemblies.push(prelude);
    compiler.compile_module(&m)
}

///Finds the main function and if it is an IO function, adds instructions to push the "RealWorld" argument
fn find_main(assembly: &Assembly) -> (Vec<Instruction>, Qualified<Type, Name>) {
    assembly.superCombinators.iter()
        .find(|sc| sc.name == Name { name: intern("main"), uid: 0 })
        .map(|sc| {
            if is_io(&sc.typ.value) {
                //If the expression we compiled is IO we need to add an extra argument
                //'RealWorld' which can be any dumb value (42 here), len - 3 is used because
                //it is currently 3 instructions Eval, Update(0), Unwind at the end of each instruction list
                //to finish the expression
                let mut vec: Vec<Instruction> = sc.instructions.iter().map(|x| x.clone()).collect();
                let len = vec.len();
                vec.insert(len - 3, Instruction::Mkap);
                vec.insert(0, Instruction::PushInt(42));//Realworld
                (vec, sc.typ.clone())
            }
            else {
                (sc.instructions.clone(), sc.typ.clone())
            }
        })
        .expect("Expected main function")
}

pub fn run_and_print_expr(expr_str: &str) {
    let prelude = compile_file("Prelude.hs");
    let mut vm = VM::new();
    vm.add_assembly(prelude);
    let assembly = compile_expr(vm.get_assembly(0), expr_str.as_slice());
    let (instructions, type_decl) = find_main(&assembly);
    let assembly_index = vm.add_assembly(assembly);
    let result = evaluate(&vm, instructions, assembly_index);//TODO 0 is not necessarily correct
    println!("{}  {}", result, type_decl);
}

///Starts the REPL
pub fn start() {
    let prelude = compile_file("Prelude.hs");
    let mut vm = VM::new();
    vm.add_assembly(prelude);
    for line in ::std::io::stdin().lines() {
        let expr_str = match line {
            Ok(l) => l,
            Err(e) => panic!("Reading line failed with '{}'", e)
        };
        let assembly = compile_expr(vm.get_assembly(0), expr_str.as_slice());
        let (instructions, typ) = find_main(&assembly);
        let assembly_index = vm.add_assembly(assembly);
        let result = evaluate(&vm, instructions, assembly_index);//TODO 0 is not necessarily correct
        println!("{}  {}", result, typ);
    }
}
