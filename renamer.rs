use std::vec::FromVec;
use module::*;
use scoped_map::ScopedMap;
use interner::*;

///A Name is a reference to a specific identifier in the program, guaranteed to be unique
#[deriving(PartialEq, Eq, Hash, Clone)]
pub struct Name {
    pub name: InternedStr,
    pub uid: uint
}

impl Str for Name {
    fn as_slice<'a>(&'a self) -> &'a str {
        self.name.as_slice()
    }
}

impl ::std::fmt::Show for Name {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}_{}", self.name, self.uid)
    }
}

///Generic struct which can store and report errors
pub struct Errors<T> {
    errors: Vec<T>
}
impl <T> Errors<T> {
    pub fn new() -> Errors<T> {
        Errors { errors: Vec::new() }
    }
    pub fn insert(&mut self, e: T) {
        self.errors.push(e);
    }
    pub fn has_errors(&self) -> bool {
        self.errors.len() != 0
    }
}
impl <T: ::std::fmt::Show> Errors<T> {
    pub fn report_errors(&self, pass: &str) {
        println!("Found {} errors in compiler pass: {}", self.errors.len(), pass);
        for error in self.errors.iter() {
            println!("{}", error);
        }
    }
}

///A NameSupply can turn simple strings into unique Names
pub struct NameSupply {
    unique_id: uint
}
impl NameSupply {
    
    pub fn new() -> NameSupply {
        NameSupply { unique_id: 0 }
    }
    ///Create a unique Name which are anonymous
    pub fn anonymous(&mut self) -> Name {
        self.from_str("_a")
    }
    ///Takes a string and returns a new Name which is unique
    pub fn from_str(&mut self, s: &str) -> Name {
        self.from_interned(intern(s))
    }
    ///Takes a string and returns a new Name which is unique
    pub fn from_interned(&mut self, s: InternedStr) -> Name {
        Name { name: s, uid: self.next_id() }
    }
    pub fn next_id(&mut self) -> uint {
        self.unique_id += 1;
        self.unique_id
    }
}

///The renamer has methods which turns the ASTs identifiers from simple strings
///into unique Names
struct Renamer {
    ///Mapping of strings into the unique name
    uniques: ScopedMap<InternedStr, Name>,
    name_supply: NameSupply,
    ///All errors found while renaming are stored here
    errors: Errors<String>
}

impl Renamer {
    fn new() -> Renamer {
        Renamer { uniques: ScopedMap::new(), name_supply: NameSupply::new(), errors: Errors::new() }
    }

    fn rename_bindings(&mut self, bindings: ~[Binding<InternedStr>], is_global: bool) -> ~[Binding<Name>] {
        //Add all bindings in the scope
        for bind in binding_groups(bindings.as_slice()) {
            self.make_unique(bind[0].name.clone());
            if is_global {
                self.uniques.find_mut(&bind[0].name).unwrap().uid = 0;
            }
        }
        FromVec::<Binding<Name>>::from_vec(bindings.move_iter().map(|binding| {
            let Binding { name: name, arguments: arguments, matches: matches, typ: typ, where: where  } = binding;
            let n = self.uniques.find(&name).map(|u| u.clone())
                .expect(format!("Error: lambda_lift: Undefined variable {}", name));
            self.uniques.enter_scope();
            let b = Binding {
                name: n,
                arguments: self.rename_arguments(arguments),
                where: where.map(|bs| self.rename_bindings(bs, false)),
                matches: self.rename_matches(matches),
                typ: typ,
            };
            self.uniques.exit_scope();
            b
        }).collect())
    }
    
    fn rename(&mut self, input_expr: TypedExpr<InternedStr>) -> TypedExpr<Name> {
        let TypedExpr { expr: expr, typ: typ, location: location } = input_expr;
        let e = match expr {
            Literal(l) => Literal(l),
            Identifier(i) => Identifier(self.get_name(i)),
            Apply(func, arg) => Apply(box self.rename(*func), box self.rename(*arg)),
            OpApply(lhs, op, rhs) => OpApply(box self.rename(*lhs), self.get_name(op), box self.rename(*rhs)),
            Lambda(arg, body) => {
                self.uniques.enter_scope();
                let l = Lambda(self.rename_pattern(arg), box self.rename(*body));
                self.uniques.exit_scope();
                l
            }
            Let(bindings, expr) => {
                self.uniques.enter_scope();
                let bs = self.rename_bindings(bindings, false);
                let l = Let(bs, box self.rename(*expr));
                self.uniques.exit_scope();
                l
            }
            Case(expr, alts) => {
                let a: Vec<Alternative<Name>> = alts.move_iter().map(|alt| {
                    let Alternative {
                        pattern: Located { location: loc, node: pattern },
                        matches: matches,
                        where: where
                    } = alt;
                    self.uniques.enter_scope();
                    let a = Alternative {
                        pattern: Located { location: loc, node: self.rename_pattern(pattern) },
                        where: where.map(|bs| self.rename_bindings(bs, false)),
                        matches: self.rename_matches(matches)
                    };
                    self.uniques.exit_scope();
                    a
                }).collect();
                Case(box self.rename(*expr), FromVec::from_vec(a))
            }
            IfElse(pred, if_true, if_false) => {
                IfElse(box self.rename(*pred),
                       box self.rename(*if_true),
                       box self.rename(*if_false))
            }
            Do(bindings, expr) => {
                let bs: Vec<DoBinding<Name>> = bindings.move_iter().map(|bind| {
                    match bind {
                        DoExpr(expr) => DoExpr(self.rename(expr)),
                        DoLet(bs) => DoLet(self.rename_bindings(bs, false)),
                        DoBind(pattern, expr) => {
                            let Located { location: location, node: node } = pattern;
                            let loc = Located { location: location, node: self.rename_pattern(node) };
                            DoBind(loc, self.rename(expr))
                        }
                    }
                }).collect();
                Do(FromVec::from_vec(bs), box self.rename(*expr))
            }
            TypeSig(expr, sig) => {
                TypeSig(box self.rename(*expr), sig)
            }
            Paren(expr) => Paren(box self.rename(*expr))
        };
        let mut t = TypedExpr::with_location(e, location);
        t.typ = typ;
        t
    }

    fn rename_pattern(&mut self, pattern: Pattern<InternedStr>) -> Pattern<Name> {
        match pattern {
            NumberPattern(i) => NumberPattern(i),
            ConstructorPattern(s, ps) => {
                let ps2: Vec<Pattern<Name>> = ps.move_iter().map(|p| self.rename_pattern(p)).collect();
                ConstructorPattern(Name { name: s, uid: 0}, FromVec::from_vec(ps2))
            }
            IdentifierPattern(s) => IdentifierPattern(self.make_unique(s)),
            WildCardPattern => WildCardPattern
        }
    }
    ///Turns the string into the Name which is currently in scope
    ///If the name was not found it is assumed to be global
    fn get_name(&self, s: InternedStr) -> Name {
        match self.uniques.find(&s) {
            Some(&Name { uid: uid, .. }) => Name { name: s, uid: uid },
            None => Name { name: s, uid: 0 }//If the variable is not found in variables it is a global variable
        }
    }

    fn rename_matches(&mut self, matches: Match<InternedStr>) -> Match<Name> {
        match matches {
            Simple(e) => Simple(self.rename(e)),
            Guards(gs) => Guards(FromVec::<Guard<Name>>::from_vec(
                gs.move_iter()
                .map(|Guard { predicate: p, expression: e }| 
                      Guard { predicate: self.rename(p), expression: self.rename(e) }
                )
                .collect()))
        }
    }

    fn rename_arguments(&mut self, arguments: ~[Pattern<InternedStr>]) -> ~[Pattern<Name>] {
        FromVec::<Pattern<Name>>::from_vec(arguments.move_iter().map(|a| self.rename_pattern(a)).collect())
    }

    ///Introduces a new Name to the current scope.
    ///If the name was already declared in the current scope an error is added
    fn make_unique(&mut self, name: InternedStr) -> Name {
        if self.uniques.in_current_scope(&name) {
            self.errors.insert(format!("{} is defined multiple times", name));
            self.uniques.find(&name).map(|x| x.clone()).unwrap()
        }
        else {
            let u = self.name_supply.from_interned(name.clone());
            self.uniques.insert(name, u.clone());
            u
        }
    }
}

pub fn rename_expr(expr: TypedExpr<InternedStr>) -> TypedExpr<Name> {
    let mut renamer = Renamer::new();
    renamer.rename(expr)
}

pub fn rename_module(module: Module<InternedStr>) -> Module<Name> {
    let mut renamer = Renamer::new();
    rename_module_(&mut renamer, module)
}
pub fn rename_module_(renamer: &mut Renamer, module: Module<InternedStr>) -> Module<Name> {
    let Module {
        name: name,
        imports: imports,
        classes : classes,
        dataDefinitions: data_definitions,
        newtypes: newtypes,
        typeDeclarations: typeDeclarations,
        bindings : bindings,
        instances: instances,
        fixity_declarations: fixity_declarations
    } = module;

    let imports2: Vec<Import<Name>> = imports.move_iter().map(|import| {
        let imports: Vec<Name> = import.imports.iter()
            .map(|&x| renamer.make_unique(x))
            .collect();
        Import { module: import.module, imports: FromVec::from_vec(imports) }
    }).collect();

    let data_definitions2 : Vec<DataDefinition<Name>> = data_definitions.move_iter().map(|data| {
        let DataDefinition {
            constructors : ctors,
            typ : typ,
            parameters : parameters,
            deriving
        } = data;
        let c: Vec<Constructor<Name>> = ctors.move_iter().map(|ctor| {
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
        }).collect();

        let d: Vec<Name> = deriving.move_iter().map(|s| {
            Name { name: s, uid: 0 }
        }).collect();

        DataDefinition {
            typ : typ,
            parameters : parameters,
            constructors : FromVec::from_vec(c),
            deriving : FromVec::from_vec(d)
        }
    }).collect();

    let newtypes2: Vec<Newtype<Name>> = newtypes.move_iter().map(|newtype| {
        let Newtype { typ: typ, constructor_name: constructor_name, constructor_type: constructor_type, deriving: deriving } = newtype;
        let deriving2: Vec<Name> = deriving.move_iter().map(|s| {
            Name { name: s, uid: 0 }
        }).collect();
        Newtype {
            typ: typ,
            constructor_name: Name { name: constructor_name, uid: 0 },
            constructor_type: constructor_type,
            deriving: FromVec::from_vec(deriving2)
        }
    }).collect();
    
    let instances2: Vec<Instance<Name>> = instances.move_iter().map(|instance| {
        let Instance {
            bindings : bindings,
            constraints : constraints,
            typ : typ,
            classname : classname
        } = instance;
        Instance {
            bindings : renamer.rename_bindings(bindings, true),
            constraints : constraints,
            typ : typ,
            classname : classname
        }
    }).collect();

    
    let classes2 : Vec<Class<Name>> = classes.move_iter().map(|class| {
        let Class {
            constraints: cs,
            name : name,
            variable : var,
            declarations : decls,
            bindings: bindings
        } = class;
        Class {
            constraints: cs,
            name: name,
            variable: var,
            declarations: decls,
            bindings: renamer.rename_bindings(bindings, true)
        }
    }).collect();
    
    let bindings2 = renamer.rename_bindings(bindings, true);

    let fixity_declarations2: Vec<FixityDeclaration<Name>> = fixity_declarations.move_iter()
        .map(|FixityDeclaration { assoc: assoc, precedence: precedence, operators: operators }| {
            
            let ops: Vec<Name> = operators.move_iter()
                .map(|s| renamer.get_name(s))
                .collect();
            FixityDeclaration { assoc: assoc, precedence: precedence,
                operators: FromVec::from_vec(ops)
            }
        })
        .collect();
    
    Module {
        name: renamer.make_unique(name),
        imports: FromVec::from_vec(imports2),
        classes : FromVec::from_vec(classes2),
        dataDefinitions: FromVec::from_vec(data_definitions2),
        typeDeclarations: typeDeclarations,
        bindings : bindings2,
        instances: FromVec::from_vec(instances2),
        newtypes: FromVec::from_vec(newtypes2),
        fixity_declarations: FromVec::from_vec(fixity_declarations2)
    }
}

///Renames a vector of modules.
///If any errors are encounterd while renaming, an error message is output and fail is called
pub fn rename_modules(modules: Vec<Module<InternedStr>>) -> Vec<Module<Name>> {
    let mut renamer = Renamer::new();
    let ms = modules.move_iter().map(|module| {
        rename_module_(&mut renamer, module)
    }).collect();
    if renamer.errors.has_errors() {
        renamer.errors.report_errors("Renamer");
        fail!();
    }
    ms
}

#[cfg(test)]
mod tests {
    use renamer::*;
    use parser::*;
    #[test]
    #[should_fail]
    fn duplicate_binding() {
        let mut parser = Parser::new(
r"main = 1
test = []
main = 2".chars());
        let module = parser.module();
        rename_modules(vec!(module));
    }
}
