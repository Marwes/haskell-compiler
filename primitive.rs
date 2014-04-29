use module::*;
use typecheck::function_type_;

pub fn primitives() -> ~[(&'static str, Type)] {
    let var = Generic(TypeVariable { id: 0, kind: StarKind } );
    let var2 = Generic(TypeVariable { id: 1, kind: StarKind } );
    ~[("error", function_type_(list_type(char_type()), var.clone())),
      ("seq", function_type_(var.clone(), function_type_(var2.clone(), var2.clone())))
    ]
}

