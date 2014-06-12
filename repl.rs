use std::vec::FromVec;
use compiler::*;
use typecheck::*;
use vm::*;
use interner::*;
use core::translate::*;
use core::*;
use lambda_lift::*;
use parser::Parser;
use renamer::{Name, rename_expr};

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

fn compile_expr(prelude: &Assembly, expr_str: &str) -> Assembly {
    let mut parser = Parser::new(expr_str.chars());
    let mut expr = rename_expr(parser.expression_());

    let mut type_env = TypeEnvironment::new();
    type_env.add_types(prelude as &DataTypes);
    type_env.typecheck_expr(&mut expr);
    let temp_module = Module::from_expr(translate_expr(expr));
    let m = do_lambda_lift(temp_module);
    
    let mut compiler = Compiler::new(&type_env);
    compiler.assemblies.push(prelude);
    compiler.compileModule(&m)
}

fn find_main(assembly: &Assembly) -> (~[Instruction], Qualified<Type>) {
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
                vec.insert(len - 3, Mkap);
                vec.insert(0, PushInt(42));//Realworld
                (FromVec::from_vec(vec), sc.typ.clone())
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

pub fn start() {
    let prelude = compile_file("Prelude.hs");
    let mut vm = VM::new();
    vm.add_assembly(prelude);
    for line in ::std::io::stdin().lines() {
        let expr_str = match line {
            Ok(l) => l,
            Err(e) => fail!("Reading line failed with '{}'", e)
        };
        let assembly = compile_expr(vm.get_assembly(0), expr_str.as_slice());
        let (instructions, typ) = find_main(&assembly);
        let assembly_index = vm.add_assembly(assembly);
        let result = evaluate(&vm, instructions, assembly_index);//TODO 0 is not necessarily correct
        println!("{}  {}", result, typ);
    }
}
