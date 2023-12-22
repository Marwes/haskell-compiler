use crate::interner::intern;
use crate::renamer::typ::*;
use crate::renamer::{name, Name};
use crate::types::{Kind, Type, TypeVariable};

///Returns an array of all the compiler primitves which exist (not including numeric primitives atm)
pub fn builtins() -> Vec<(&'static str, Type<Name>)> {
    let var = Type::Generic(TypeVariable {
        id: intern("a"),
        kind: Kind::Star,
        age: 0,
    });
    let var2 = Type::Generic(TypeVariable {
        id: intern("b"),
        kind: Kind::Star,
        age: 0,
    });
    vec![
        ("error", function_type_(list_type(char_type()), var.clone())),
        (
            "seq",
            function_type_(var.clone(), function_type_(var2.clone(), var2.clone())),
        ),
        (
            "readFile",
            function_type_(list_type(char_type()), io(list_type(char_type()))),
        ),
        (
            "io_bind",
            function_type_(
                io(var.clone()),
                function_type_(
                    function_type_(var.clone(), io(var2.clone())),
                    io(var2.clone()),
                ),
            ),
        ),
        ("io_return", function_type_(var.clone(), io(var.clone()))),
        (
            "putStrLn",
            function_type_(list_type(char_type()), io(unit())),
        ),
        (
            "#compare_tags",
            function_type_(
                var.clone(),
                function_type_(var.clone(), Type::new_op(name("Ordering"), vec![])),
            ),
        ),
    ]
}
