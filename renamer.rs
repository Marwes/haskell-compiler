use module::*;
use scoped_map::ScopedMap;

#[deriving(Eq, TotalEq, Hash, Clone, Show)]
pub struct Name {
    pub name: ~str,
    pub uid: uint
}

struct Renamer {
    uniques: ScopedMap<~str, Name>,
    unique_id: uint
}

impl Renamer {

    fn rename_bindings(&mut self, bindings: ~[Binding<~str>]) -> ~[Binding<Name>] {
        //Add all bindings in the scope
        for bind in bindings.iter() {
            self.make_unique(bind.name.clone());
        }
        bindings.move_iter().map(|binding| {
            let Binding { name: name, expression: expression, typeDecl: typeDecl, arity: arity  } = binding;
            let n = self.uniques.find(&name).map(|u| u.clone())
                .expect(format!("Error: lambda_lift: Undefined variable {}", name));
            Binding {
                name: n,
                expression: self.rename(expression),
                typeDecl: typeDecl,
                arity: arity
            }
        }).collect()
    }

    fn rename(&mut self, input_expr: TypedExpr<~str>) -> TypedExpr<Name> {
        let TypedExpr { expr: expr, typ: typ, location: location } = input_expr;
        let e = match expr {
            Number(n) => Number(n),
            Rational(r) => Rational(r),
            String(s) => String(s),
            Char(c) => Char(c),
            Identifier(i) => {
                let n = match self.uniques.find(&i).map(|u| u.clone()) {
                    Some(n) => n,
                    None => Name { name: i, uid: 0 }//If the variable is not found in variables it is a global variable
                };
                Identifier(n)
            }
            Apply(func, arg) => Apply(~self.rename(*func), ~self.rename(*arg)),
            Lambda(arg, body) => {
                self.uniques.enter_scope();
                let l = Lambda(self.make_unique(arg), ~self.rename(*body));
                self.uniques.exit_scope();
                l
            }
            Let(bindings, expr) => {
                self.uniques.enter_scope();
                let bs = self.rename_bindings(bindings);
                let l = Let(bs, ~self.rename(*expr));
                self.uniques.exit_scope();
                l
            }
            Case(expr, alts) => {
                let a = alts.move_iter().map(
                    |Alternative { pattern: Located { location: loc, node: pattern }, expression: expression }| {
                    self.uniques.enter_scope();
                    let a = Alternative {
                        pattern: Located { location: loc, node: self.rename_pattern(pattern) },
                        expression: self.rename(expression)
                    };
                    self.uniques.exit_scope();
                    a
                }).collect();
                Case(~self.rename(*expr), a)
            }
        };
        let mut t = TypedExpr::with_location(e, location);
        t.typ = typ;
        t
    }

    fn rename_pattern(&mut self, pattern: Pattern<~str>) -> Pattern<Name> {
        match pattern {
            NumberPattern(i) => NumberPattern(i),
            ConstructorPattern(s, ps) => {
                let ps2 = ps.move_iter().map(|p| self.rename_pattern(p)).collect();
                ConstructorPattern(s, ps2)
            }
            IdentifierPattern(s) => IdentifierPattern(self.make_unique(s))
        }
    }

    fn make_unique(&mut self, name: ~str) -> Name {
        self.unique_id += 1;
        let u = Name { name: name.clone(), uid: self.unique_id};
        self.uniques.insert(name, u.clone());
        u
    }
}
