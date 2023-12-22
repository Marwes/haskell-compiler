use crate::{
    core::{
        Expr::*,
        *,
    },
    interner::{
        intern,
        InternedStr,
    },
    module::encode_binding_identifier,
    renamer::{
        name,
        typ::*,
        NameSupply,
    },
};

pub fn generate_deriving(instances: &mut Vec<Instance<Id<Name>>>, data: &DataDefinition<Name>) {
    let mut gen =
        DerivingGen {
            name_supply: NameSupply::new(),
        };
    for deriving in data.deriving.iter() {
        match deriving.as_ref() {
            "Eq" => {
                let mut bindings = vec![];
                bindings.push(gen.generate_eq(data));
                instances.push(Instance {
                    constraints: vec![],
                    typ: data.typ.value.clone(),
                    classname: "Eq".into(),
                    bindings,
                });
            }
            "Ord" => {
                let mut bindings = vec![];
                let b = gen.generate_ord(data);
                debug!("Generated Ord {:?} ->>\n{:?}", data.typ, b);
                bindings.push(b);
                instances.push(Instance {
                    constraints: vec![],
                    typ: data.typ.value.clone(),
                    classname: "Ord".into(),
                    bindings,
                });
            }
            x => panic!("Cannot generate instance for class {:?}", x),
        }
    }
}

struct DerivingGen {
    name_supply: NameSupply,
}
impl DerivingGen {
    fn generate_eq(&mut self, data: &DataDefinition<Name>) -> Binding<Id<Name>> {
        self.make_binop("Eq", "==", data, &mut |this, id_l, id_r| {
            let alts =
                this.match_same_constructors(data, &id_r, &mut |this, l, r| this.eq_fields(l, r));
            Case(Box::new(Identifier(id_l.clone())), alts)
        })
    }

    fn eq_fields(&mut self, args_l: &[Id<Name>], args_r: &[Id<Name>]) -> Expr<Id<Name>> {
        if args_l.len() >= 1 {
            let first = bool_binop(
                "==",
                Identifier(args_l[0].clone()),
                Identifier(args_r[0].clone()),
            );
            args_l
                .iter()
                .skip(1)
                .zip(args_r.iter().skip(1))
                .fold(first, |acc, (l, r)| {
                    let test = bool_binop("==", Identifier(l.clone()), Identifier(r.clone()));
                    bool_binop("&&", acc, test)
                })
        } else {
            true_expr()
        }
    }

    fn generate_ord(&mut self, data: &DataDefinition<Name>) -> Binding<Id<Name>> {
        self.make_binop("Ord", "compare", data, &mut |this, id_l, id_r| {
            //We first compare the tags of the arguments since this would otherwise the last of the alternatives
            let when_eq = {
                let alts = this
                    .match_same_constructors(data, &id_r, &mut |this, l, r| this.ord_fields(l, r));
                Case(Box::new(Identifier(id_l.clone())), alts)
            };
            let cmp = compare_tags(Identifier(id_l), Identifier(id_r));
            this.eq_or_default(cmp, when_eq)
        })
    }

    fn ord_fields(&mut self, args_l: &[Id<Name>], args_r: &[Id<Name>]) -> Expr<Id<Name>> {
        let ordering = Type::new_op(name("Ordering"), vec![]);
        if args_l.len() >= 1 {
            let mut iter = args_l.iter().zip(args_r.iter()).rev();
            let (x, y) = iter.next().unwrap();
            let last = binop(
                "compare",
                Identifier(x.clone()),
                Identifier(y.clone()),
                ordering.clone(),
            );
            iter.fold(last, |acc, (l, r)| {
                let test = bool_binop("compare", Identifier(l.clone()), Identifier(r.clone()));
                self.eq_or_default(test, acc)
            })
        } else {
            Identifier(id("EQ", ordering))
        }
    }

    ///Creates a binary function binding with the name 'funcname' which is a function in an instance for 'data'
    ///This function takes two parameters of the type of 'data'
    fn make_binop(
        &mut self,
        class: &str,
        funcname: &str,
        data: &DataDefinition<Name>,
        func: &mut dyn FnMut(&mut DerivingGen, Id<Name>, Id<Name>) -> Expr<Id<Name>>,
    ) -> Binding<Id<Name>> {
        let arg_l = self.name_supply.anonymous();
        let arg_r = self.name_supply.anonymous();
        let mut id_r = Id::new(arg_r, data.typ.value.clone(), data.typ.constraints.clone());
        let mut id_l = Id::new(arg_l, data.typ.value.clone(), data.typ.constraints.clone());
        let expr = func(self, id_l.clone(), id_r.clone());
        id_r.typ.value = function_type_(data.typ.value.clone(), bool_type());
        id_l.typ.value = function_type_(
            data.typ.value.clone(),
            function_type_(data.typ.value.clone(), bool_type()),
        );
        let lambda_expr = Lambda(id_l, Box::new(Lambda(id_r, Box::new(expr)))); //TODO types
        let data_name = extract_applied_type(&data.typ.value).ctor().name;
        let name = encode_binding_identifier(data_name.name, intern(funcname));
        //Create a constraint for each type parameter
        fn make_constraints(
            mut result: Vec<Constraint<Name>>,
            class: InternedStr,
            typ: &Type<Name>,
        ) -> Vec<Constraint<Name>> {
            match typ {
                &Type::Application(ref f, ref param) => {
                    result.push(Constraint {
                        class: Name {
                            name: class,
                            uid: 0,
                        },
                        variables: vec![param.var().clone()],
                    });
                    make_constraints(result, class, &**f)
                }
                _ => result,
            }
        }
        let constraints = make_constraints(vec![], intern(class), &data.typ.value);
        Binding {
            name: Id::new(
                Name { name, uid: 0 },
                lambda_expr.get_type().clone(),
                constraints,
            ),
            expression: lambda_expr,
        }
    }

    fn eq_or_default(&mut self, cmp: Expr<Id<Name>>, def: Expr<Id<Name>>) -> Expr<Id<Name>> {
        let match_id = Id::new(
            self.name_supply.anonymous(),
            Type::new_op(name("Ordering"), vec![]),
            vec![],
        );
        Case(
            Box::new(cmp),
            vec![
                Alternative {
                    pattern: Pattern::Constructor(
                        id("EQ", Type::new_op(name("Ordering"), vec![])),
                        vec![],
                    ),
                    expression: def,
                },
                Alternative {
                    pattern: Pattern::Identifier(match_id.clone()),
                    expression: Identifier(match_id),
                },
            ],
        )
    }

    fn match_same_constructors(
        &mut self,
        data: &DataDefinition<Name>,
        id_r: &Id<Name>,
        f: &mut dyn FnMut(&mut DerivingGen, &[Id<Name>], &[Id<Name>]) -> Expr<Id<Name>>,
    ) -> Vec<Alternative<Id<Name>>> {
        let alts: Vec<Alternative<Id<Name>>> = data
            .constructors
            .iter()
            .map(|constructor| {
                let args_l: Vec<Id<Name>> = ArgIterator {
                    typ: &constructor.typ.value,
                }
                .map(|arg| {
                    Id::new(
                        self.name_supply.anonymous(),
                        arg.clone(),
                        constructor.typ.constraints.clone(),
                    )
                })
                .collect();
                let mut iter = ArgIterator {
                    typ: &constructor.typ.value,
                };
                let args_r: Vec<Id<Name>> = iter
                    .by_ref()
                    .map(|arg| {
                        Id::new(
                            self.name_supply.anonymous(),
                            arg.clone(),
                            constructor.typ.constraints.clone(),
                        )
                    })
                    .collect();
                let ctor_id = Id::new(
                    constructor.name,
                    iter.typ.clone(),
                    constructor.typ.constraints.clone(),
                );
                let expr = f(self, &*args_l, &*args_r);
                let pattern_r = Pattern::Constructor(ctor_id.clone(), args_r);
                let inner = Case(
                    Box::new(Identifier(id_r.clone())),
                    vec![
                        Alternative {
                            pattern: pattern_r,
                            expression: expr,
                        },
                        Alternative {
                            pattern: Pattern::WildCard,
                            expression: Identifier(Id::new("False".into(), bool_type(), vec![])),
                        },
                    ],
                );
                Alternative {
                    pattern: Pattern::Constructor(ctor_id, args_l),
                    expression: inner,
                }
            })
            .collect();
        alts
    }
}

fn id(s: &str, typ: Type<Name>) -> Id<Name> {
    Id::new(s.into(), typ, vec![])
}

fn compare_tags(lhs: Expr<Id<Name>>, rhs: Expr<Id<Name>>) -> Expr<Id<Name>> {
    let var = Type::new_var(intern("a"));
    let typ = function_type_(
        var.clone(),
        function_type_(var.clone(), Type::new_op(name("Ordering"), vec![])),
    );
    let id = Id::new(name("#compare_tags"), typ, vec![]);
    Apply(
        Box::new(Apply(Box::new(Identifier(id)), Box::new(lhs))),
        Box::new(rhs),
    )
}

fn bool_binop(op: &str, lhs: Expr<Id<Name>>, rhs: Expr<Id<Name>>) -> Expr<Id<Name>> {
    binop(op, lhs, rhs, bool_type())
}
fn binop(
    op: &str,
    lhs: Expr<Id<Name>>,
    rhs: Expr<Id<Name>>,
    return_type: Type<Name>,
) -> Expr<Id<Name>> {
    let typ = function_type_(
        lhs.get_type().clone(),
        function_type_(rhs.get_type().clone(), return_type),
    );
    let f = Identifier(Id::new(name(op), typ, vec![]));
    Apply(Box::new(Apply(Box::new(f), Box::new(lhs))), Box::new(rhs))
}

fn true_expr() -> Expr<Id<Name>> {
    Identifier(Id::new(name("True"), bool_type(), vec![]))
}

struct ArgIterator<'a> {
    typ: &'a Type<Name>,
}
impl<'a> Iterator for ArgIterator<'a> {
    type Item = &'a Type<Name>;
    fn next(&mut self) -> Option<&'a Type<Name>> {
        use crate::types::try_get_function;
        match try_get_function(self.typ) {
            Some((arg, rest)) => {
                self.typ = rest;
                Some(arg)
            }
            None => None,
        }
    }
}
fn extract_applied_type<'a, Id>(typ: &'a Type<Id>) -> &'a Type<Id> {
    match typ {
        &Type::Application(ref lhs, _) => extract_applied_type(&**lhs),
        _ => typ,
    }
}
