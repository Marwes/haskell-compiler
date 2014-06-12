use types::*;
use interner::intern;

///Returns an array of all the compiler primitves which exist (not including numeric primitives atm)
pub fn primitives() -> ~[(&'static str, Type)] {
    let var = Generic(TypeVariable { id: intern("a"), kind: StarKind, age: 0 } );
    let var2 = Generic(TypeVariable { id: intern("b"), kind: StarKind, age: 0 } );
    ~[("error", function_type_(list_type(char_type()), var.clone())),
      ("seq", function_type_(var.clone(), function_type_(var2.clone(), var2.clone()))),
      ("readFile", function_type_(list_type(char_type()), io(list_type(char_type())))),
      ("io_bind", function_type_(io(var.clone()),
                  function_type_(function_type_(var.clone(), io(var2.clone())),
                                 io(var2.clone())))),
      ("io_return", function_type_(var.clone(), io(var.clone()))),
      ("putStrLn", function_type_(list_type(char_type()), io(unit()))),
    ]
}

