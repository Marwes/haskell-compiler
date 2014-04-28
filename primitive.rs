use module::*;
use typecheck::function_type_;

pub fn primitives() -> ~[(&'static str, Type)] {
    let var = Generic(TypeVariable { id: 0, kind: StarKind } );
    ~[("error", function_type_(list_type(char_type()), var.clone()))
    ]
}

