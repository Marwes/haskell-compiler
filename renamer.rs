use module::*;
use scoped_map::ScopedMap;

#[deriving(Eq, TotalEq, Hash, Clone, Show)]
pub struct Name {
    pub name: ~str,
    pub uid: uint
}

impl Str for Name {
    fn as_slice<'a>(&'a self) -> &'a str {
        self.name.as_slice()
    }
    fn into_owned(self) -> ~str {
        self.name
    }
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
            Identifier(i) => Identifier(self.get_name(i)),
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
                ConstructorPattern(Name { name: s, uid: 0}, ps2)
            }
            IdentifierPattern(s) => IdentifierPattern(self.make_unique(s))
        }
    }
    fn get_name(&self, s: ~str) -> Name {
        match self.uniques.find(&s) {
            Some(&Name { uid: uid, .. }) => Name { name: s, uid: uid },
            None => Name { name: s, uid: 0 }//If the variable is not found in variables it is a global variable
        }
    }

    fn rename_binding(&mut self, binding: Binding<~str>) -> Binding<Name> {
        let Binding { name: name, expression: expression, typeDecl: td, arity: a } = binding;
        Binding {
            name: Name { name: name, uid: 0 },
            expression: self.rename(expression),
            typeDecl: td,
            arity: a
        }
    }


    fn make_unique(&mut self, name: ~str) -> Name {
        self.unique_id += 1;
        let u = Name { name: name.clone(), uid: self.unique_id};
        self.uniques.insert(name, u.clone());
        u
    }
}
pub fn rename_expr(expr: TypedExpr<~str>) -> TypedExpr<Name> {
    let mut renamer = Renamer { uniques: ScopedMap::new(), unique_id: 1 };
    renamer.rename(expr)
}

pub fn rename_module(module: Module<~str>) -> Module<Name> {
    let mut renamer = Renamer { uniques: ScopedMap::new(), unique_id: 1 };
    let Module {
        name: name,
        classes : classes,
        dataDefinitions: data_definitions,
        typeDeclarations: typeDeclarations,
        bindings : bindings,
        instances: instances
    } = module;

    let data_definitions2 = data_definitions.move_iter().map(|data| {
        let DataDefinition {
            constructors : ctors,
            typ : typ,
            parameters : parameters
        } = data;
        DataDefinition {
            typ : typ,
            parameters : parameters,
            constructors : ctors.move_iter().map(|ctor| {
                let Constructor {
                    name : name,
                    typ : typ,
                    tag : tag,
                    arity : arity
                } = ctor;
                Constructor {
                    name : Name { name: name, uid: 0 },
                    typ : typ,
                    tag : tag,
                    arity : arity
                }
            }).collect()
        }
    }).collect();
    
    let instances2 = instances.move_iter().map(|instance| {
        let Instance {
            bindings : bindings,
            constraints : constraints,
            typ : typ,
            classname : classname
        } = instance;
        Instance {
            bindings : bindings.move_iter().map(|b| renamer.rename_binding(b)).collect(),
            constraints : constraints,
            typ : typ,
            classname : classname
        }
    }).collect();
    
    let bindings2 : ~[Binding<Name>] = bindings.move_iter().map(|b| renamer.rename_binding(b)).collect();
    
    Module {
        name: renamer.make_unique(name),
        classes : classes,
        dataDefinitions: data_definitions2,
        typeDeclarations: typeDeclarations,
        bindings : bindings2,
        instances: instances2
    }
}

