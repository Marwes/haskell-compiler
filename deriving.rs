use module::{DataDefinition, encode_binding_identifier};
use core::*;
use renamer::{Name, NameSupply};
use types::*;
use interner::intern;

use std::vec::FromVec;

pub fn generate_deriving(bindings: &mut Vec<Binding<Id<Name>>>, data: &DataDefinition<Name>) {
    let mut gen = DerivingGen { name_supply: NameSupply::new() };
    for deriving in data.deriving.iter() {
        match deriving.as_slice() {
            "Eq" => {
                bindings.push(gen.generate_eq(data));
            }
            x => fail!("Cannot generate instance for class {}", x)
        }
    }
}

struct DerivingGen {
    name_supply: NameSupply
}
impl DerivingGen {
    fn generate_eq(&mut self, data: &DataDefinition<Name>) -> Binding<Id<Name>> {
        let arg_l = self.name_supply.anonymous();
        let arg_r = self.name_supply.anonymous();
        let id_r = Id::new(arg_r, data.typ.value.clone(), data.typ.constraints.clone());
        let alts: Vec<Alternative<Id<Name>>> = data.constructors.iter().map(|constructor| {
            let args_l: ~[Id<Name>] = FromVec::<Id<Name>>::from_vec(
                ArgIterator { typ: &constructor.typ.value }
                .map(|arg| Id::new(self.name_supply.anonymous(), arg.clone(), constructor.typ.constraints.clone()))
                .collect());
            let iter = ArgIterator { typ: &constructor.typ.value };
            let args_r: ~[Id<Name>] = FromVec::<Id<Name>>::from_vec(iter
                .map(|arg| Id::new(self.name_supply.anonymous(), arg.clone(), constructor.typ.constraints.clone()))
                .collect());
            let ctor_id = Id::new(constructor.name, iter.typ.clone(), constructor.typ.constraints.clone());
            let expr = self.eq_fields(&constructor.typ, args_l, args_r);
            let pattern_r = ConstructorPattern(ctor_id.clone(), args_r);
            let id_r = Id::new(arg_r, iter.typ.clone(), constructor.typ.constraints.clone());
            let inner = Case(box Identifier(id_r), box [
                Alternative { pattern: pattern_r, expression: expr },
                Alternative { 
                    pattern: WildCardPattern,
                    expression: Identifier(Id::new(Name { uid: 0, name: intern("False") }, bool_type(), box []))
                }
            ]);
            Alternative { pattern: ConstructorPattern(ctor_id, args_l), expression: inner }
        }).collect();
        let id_l = Id::new(arg_l, data.typ.value.clone(), data.typ.constraints.clone());
        let expr = Case(box Identifier(id_l.clone()), FromVec::from_vec(alts));
        let eq_expr = Lambda(id_l, box Lambda(id_r, box expr));//TODO types
        let data_name = extract_applied_type(&data.typ.value).ctor().name;
        let eq_name = encode_binding_identifier(data_name, intern("=="));
        let eq_bind = Binding {
            name: Id::new(Name { name: eq_name, uid: 0 }, eq_expr.get_type().clone(), box []),
            expression: eq_expr
        };
        eq_bind
    }

    fn eq_fields(&mut self, typ: &Qualified<Type>, args_l: &[Id<Name>], args_r: &[Id<Name>]) -> Expr<Id<Name>> {
        if args_l.len() >= 1 {
            let first = bool_binop("==", Identifier(args_l[0].clone()), Identifier(args_r[0].clone()));
            args_l.iter().skip(1).zip(args_r.iter().skip(1)).fold(first, |acc, (l, r)| {
                let test = bool_binop("==", Identifier(l.clone()), Identifier(r.clone()));
                bool_binop("&&", acc, test)
            })
        }
        else {
            true_expr()
        }
    }
}

fn bool_binop(op: &str, lhs: Expr<Id<Name>>, rhs: Expr<Id<Name>>) -> Expr<Id<Name>> {
    let typ = function_type_(lhs.get_type().clone(), function_type_(rhs.get_type().clone(), bool_type()));
    let f = Identifier(Id::new(Name { name: intern(op), uid: 0 }, typ, box []));
    Apply(box Apply(box f, box lhs), box rhs)
}

fn true_expr() -> Expr<Id<Name>> { 
    Identifier(Id::new(Name { uid: 0, name: intern("True") }, bool_type(), box []))
}

struct ArgIterator<'a> {
    typ: &'a Type
}
impl <'a> Iterator<&'a Type> for ArgIterator<'a> {
    fn next(&mut self) -> Option<&'a Type> {
        use types::try_get_function;
        match try_get_function(self.typ) {
            Some((arg, rest)) => {
                self.typ = rest;
                Some(arg)
            }
            None => None
        }
    }
}
fn extract_applied_type<'a>(typ: &'a Type) -> &'a Type {
    match typ {
        &TypeApplication(ref lhs, _) => extract_applied_type(*lhs),
        _ => typ
    }
}
