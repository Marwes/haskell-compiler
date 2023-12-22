use crate::interner::*;
use crate::lexer::Located;
use crate::module::*;
use crate::scoped_map::ScopedMap;
use std::error;
use std::fmt;

///A Name is a reference to a specific identifier in the program, guaranteed to be unique
#[derive(Eq, Hash, Clone, Copy, Debug)]
pub struct Name {
    pub name: InternedStr,
    pub uid: usize,
}

pub fn name(s: &str) -> Name {
    Name {
        uid: 0,
        name: intern(s),
    }
}

impl PartialEq<Name> for Name {
    fn eq(&self, other: &Name) -> bool {
        self.uid == other.uid && self.name == other.name
    }
}
impl PartialEq<InternedStr> for Name {
    fn eq(&self, other: &InternedStr) -> bool {
        self.name == *other
    }
}
impl PartialEq<Name> for InternedStr {
    fn eq(&self, other: &Name) -> bool {
        *self == other.name
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        self.name.as_ref()
    }
}

impl ::std::fmt::Display for Name {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}_{}", self.name, self.uid)
    }
}

///Generic struct which can store and report errors
#[derive(Debug)]
pub struct Errors<T> {
    errors: Vec<T>,
}
impl<T> Errors<T> {
    pub fn new() -> Errors<T> {
        Errors { errors: vec![] }
    }
    pub fn insert(&mut self, e: T) {
        self.errors.push(e);
    }
    pub fn has_errors(&self) -> bool {
        self.errors.len() != 0
    }

    pub fn into_result<V>(&mut self, value: V) -> Result<V, Errors<T>> {
        if self.has_errors() {
            Err(::std::mem::replace(self, Errors::new()))
        } else {
            Ok(value)
        }
    }
}
impl<T: fmt::Display> Errors<T> {
    pub fn report_errors(&self, f: &mut fmt::Formatter, pass: &str) -> fmt::Result {
        write!(
            f,
            "Found {} errors in compiler pass: {}",
            self.errors.len(),
            pass
        )?;
        for error in self.errors.iter() {
            write!(f, "{}", error)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct RenamerError(Errors<Error>);

impl fmt::Display for RenamerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.report_errors(f, "renamer")
    }
}

impl error::Error for RenamerError {
    fn description(&self) -> &str {
        "renaming error"
    }
}

#[derive(Debug)]
enum Error {
    MultipleDefinitions(InternedStr),
    UndefinedModule(InternedStr),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::MultipleDefinitions(s) => write!(f, "{} is defined multiple times", s),
            Error::UndefinedModule(s) => write!(f, "Module {} is not defined", s),
        }
    }
}

///A NameSupply can turn simple strings into unique Names
pub struct NameSupply {
    unique_id: usize,
}
impl NameSupply {
    pub fn new() -> NameSupply {
        NameSupply { unique_id: 1 }
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
        Name {
            name: s,
            uid: self.next_id(),
        }
    }
    pub fn next_id(&mut self) -> usize {
        self.unique_id += 1;
        self.unique_id
    }
}

///The renamer has methods which turns the ASTs identifiers from simple strings
///into unique Names
///Currently there is some constraints on what the unique ids should be.
///Each module gets one uid which it uses for a top level declarations (bindings, types, etc)
///All functions which are in a class or an instance gets the same id as the class has,
///this is to allow the compiler to find the specific instance/class functions when it constructs dictionaries
///All uid's of the other names can have any uid (as long as it isizeroduces no name collisions)
struct Renamer {
    ///Mapping of strings into the unique name
    uniques: ScopedMap<InternedStr, Name>,
    name_supply: NameSupply,
    ///All errors found while renaming are stored here
    errors: Errors<Error>,
}

impl Renamer {
    fn new() -> Renamer {
        Renamer {
            uniques: ScopedMap::new(),
            name_supply: NameSupply::new(),
            errors: Errors::new(),
        }
    }

    fn import_globals<T: Eq + Copy>(
        &mut self,
        module: &Module<T>,
        str_fn: &mut dyn FnMut(T) -> InternedStr,
        uid: usize,
    ) {
        let names = module
            .data_definitions
            .iter()
            .flat_map(|data| data.constructors.iter().map(|ctor| ctor.name))
            .chain(
                module
                    .newtypes
                    .iter()
                    .map(|newtype| newtype.constructor_name),
            )
            .chain(module.classes.iter().flat_map(|class| {
                Some(class.name)
                    .into_iter()
                    .chain(class.declarations.iter().map(|decl| decl.name))
                    .chain(binding_groups(&*class.bindings).map(|binds| binds[0].name))
            }))
            .chain(binding_groups(module.bindings.as_ref()).map(|binds| binds[0].name));
        for name in names {
            self.declare_global(str_fn(name), uid);
        }
        for instance in module.instances.iter() {
            let class_uid = self.get_name(str_fn(instance.classname)).uid;
            for binds in binding_groups(instance.bindings.as_ref()) {
                self.declare_global(str_fn(binds[0].name), class_uid);
            }
        }
    }

    ///Puts the globals of `module_env` into the current scope of the renamer.
    ///This includes putting all globals from the imports and the the globals of the module itself
    ///into scope
    fn insert_globals(
        &mut self,
        module_env: &[Module<Name>],
        module: &Module<InternedStr>,
        uid: usize,
    ) {
        self.import_globals(module, &mut |name| name, uid);
        for import in module.imports.iter() {
            let imported_module = module_env.iter().find(|m| m.name.name == import.module);
            let imported_module = match imported_module {
                Some(x) => x,
                None => {
                    self.errors.insert(Error::UndefinedModule(import.module));
                    continue;
                }
            };
            let uid = imported_module.name.uid;
            match import.imports {
                Some(ref imports) => {
                    for &imported_str in imports.iter() {
                        self.declare_global(imported_str, uid);
                    }
                }
                None => {
                    //Import everything
                    self.import_globals(
                        imported_module,
                        &mut |name| name.name,
                        imported_module.name.uid,
                    )
                }
            }
        }
    }

    fn rename_bindings(
        &mut self,
        bindings: Vec<Binding<InternedStr>>,
        is_global: bool,
    ) -> Vec<Binding<Name>> {
        //Add all bindings in the scope
        if !is_global {
            for bind in binding_groups(bindings.as_ref()) {
                self.make_unique(bind[0].name.clone());
            }
        }
        bindings
            .into_iter()
            .map(|binding| {
                let Binding {
                    name,
                    arguments,
                    matches,
                    typ,
                    where_bindings,
                } = binding;
                let n = self.uniques.find(&name).map(|u| u.clone()).unwrap_or_else(
                    || unreachable!("Variable {} should already have been defined", name)
                );
                self.uniques.enter_scope();
                let b = Binding {
                    name: n,
                    arguments: self.rename_arguments(arguments),
                    where_bindings: where_bindings.map(|bs| self.rename_bindings(bs, false)),
                    matches: self.rename_matches(matches),
                    typ: self.rename_qualified_type(typ),
                };
                self.uniques.exit_scope();
                b
            })
            .collect()
    }

    fn rename(&mut self, input_expr: TypedExpr<InternedStr>) -> TypedExpr<Name> {
        use crate::module::DoBinding::*;
        use crate::module::Expr::*;
        let TypedExpr {
            expr,
            typ,
            location,
        } = input_expr;
        let e = match expr {
            Literal(l) => Literal(l),
            Identifier(i) => Identifier(self.get_name(i)),
            Apply(func, arg) => Apply(Box::new(self.rename(*func)), Box::new(self.rename(*arg))),
            OpApply(lhs, op, rhs) => OpApply(
                Box::new(self.rename(*lhs)),
                self.get_name(op),
                Box::new(self.rename(*rhs)),
            ),
            Lambda(arg, body) => {
                self.uniques.enter_scope();
                let l = Lambda(self.rename_pattern(arg), Box::new(self.rename(*body)));
                self.uniques.exit_scope();
                l
            }
            Let(bindings, expr) => {
                self.uniques.enter_scope();
                let bs = self.rename_bindings(bindings, false);
                let l = Let(bs, Box::new(self.rename(*expr)));
                self.uniques.exit_scope();
                l
            }
            Case(expr, alts) => {
                let a: Vec<Alternative<Name>> = alts
                    .into_iter()
                    .map(|alt| {
                        let Alternative {
                            pattern:
                                Located {
                                    location: loc,
                                    node: pattern,
                                },
                            matches,
                            where_bindings,
                        } = alt;
                        self.uniques.enter_scope();
                        let a = Alternative {
                            pattern: Located {
                                location: loc,
                                node: self.rename_pattern(pattern),
                            },
                            where_bindings: where_bindings
                                .map(|bs| self.rename_bindings(bs, false)),
                            matches: self.rename_matches(matches),
                        };
                        self.uniques.exit_scope();
                        a
                    })
                    .collect();
                Case(Box::new(self.rename(*expr)), a)
            }
            IfElse(pred, if_true, if_false) => IfElse(
                Box::new(self.rename(*pred)),
                Box::new(self.rename(*if_true)),
                Box::new(self.rename(*if_false)),
            ),
            Do(bindings, expr) => {
                let bs: Vec<DoBinding<Name>> = bindings
                    .into_iter()
                    .map(|bind| match bind {
                        DoExpr(expr) => DoExpr(self.rename(expr)),
                        DoLet(bs) => DoLet(self.rename_bindings(bs, false)),
                        DoBind(pattern, expr) => {
                            let Located { location, node } = pattern;
                            let loc = Located {
                                location,
                                node: self.rename_pattern(node),
                            };
                            DoBind(loc, self.rename(expr))
                        }
                    })
                    .collect();
                Do(bs, Box::new(self.rename(*expr)))
            }
            TypeSig(expr, sig) => TypeSig(
                Box::new(self.rename(*expr)),
                self.rename_qualified_type(sig),
            ),
            Paren(expr) => Paren(Box::new(self.rename(*expr))),
        };
        let mut t = TypedExpr::with_location(e, location);
        t.typ = self.rename_type(typ);
        t
    }

    fn rename_pattern(&mut self, pattern: Pattern<InternedStr>) -> Pattern<Name> {
        match pattern {
            Pattern::Number(i) => Pattern::Number(i),
            Pattern::Constructor(s, ps) => {
                let ps2: Vec<Pattern<Name>> =
                    ps.into_iter().map(|p| self.rename_pattern(p)).collect();
                Pattern::Constructor(self.get_name(s), ps2)
            }
            Pattern::Identifier(s) => Pattern::Identifier(self.make_unique(s)),
            Pattern::WildCard => Pattern::WildCard,
        }
    }
    ///Turns the string into the Name which is currently in scope
    ///If the name was not found it is assumed to be global
    fn get_name(&self, s: InternedStr) -> Name {
        match self.uniques.find(&s) {
            Some(&Name { uid, .. }) => Name { name: s, uid: uid },
            None => Name { name: s, uid: 0 }, //Primitive
        }
    }

    fn rename_matches(&mut self, matches: Match<InternedStr>) -> Match<Name> {
        match matches {
            Match::Simple(e) => Match::Simple(self.rename(e)),
            Match::Guards(gs) => Match::Guards(
                gs.into_iter()
                    .map(
                        |Guard {
                             predicate: p,
                             expression: e,
                         }| Guard {
                            predicate: self.rename(p),
                            expression: self.rename(e),
                        },
                    )
                    .collect(),
            ),
        }
    }

    fn rename_arguments(&mut self, arguments: Vec<Pattern<InternedStr>>) -> Vec<Pattern<Name>> {
        arguments
            .into_iter()
            .map(|a| self.rename_pattern(a))
            .collect()
    }

    fn rename_qualified_type(
        &mut self,
        typ: Qualified<Type<InternedStr>, InternedStr>,
    ) -> Qualified<Type<Name>, Name> {
        let Qualified {
            constraints,
            value: typ,
        } = typ;
        let constraints2: Vec<Constraint<Name>> = constraints
            .into_iter()
            .map(|Constraint { class, variables }| Constraint {
                class: self.get_name(class),
                variables,
            })
            .collect();
        qualified(constraints2, self.rename_type(typ))
    }
    fn rename_type_declarations(
        &mut self,
        decls: Vec<TypeDeclaration<InternedStr>>,
    ) -> Vec<TypeDeclaration<Name>> {
        let decls2: Vec<TypeDeclaration<Name>> = decls
            .into_iter()
            .map(|decl| TypeDeclaration {
                name: self.get_name(decl.name),
                typ: self.rename_qualified_type(decl.typ),
            })
            .collect();
        decls2
    }

    ///Introduces a new Name to the current scope.
    ///If the name was already declared in the current scope an error is added
    fn make_unique(&mut self, name: InternedStr) -> Name {
        if self.uniques.in_current_scope(&name) {
            self.errors.insert(Error::MultipleDefinitions(name));
            self.uniques.find(&name).map(|x| x.clone()).unwrap()
        } else {
            let u = self.name_supply.from_interned(name.clone());
            self.uniques.insert(name, u.clone());
            u
        }
    }
    fn declare_global(&mut self, s: InternedStr, module_id: usize) -> Name {
        self.make_unique(s);
        let name = self.uniques.find_mut(&s).unwrap();
        name.uid = module_id;
        *name
    }

    fn rename_type(&mut self, typ: Type<InternedStr>) -> Type<Name> {
        typ.map(|s| self.get_name(s))
    }
}

pub fn rename_expr(expr: TypedExpr<InternedStr>) -> Result<TypedExpr<Name>, RenamerError> {
    let mut renamer = Renamer::new();
    let expr = renamer.rename(expr);
    renamer.errors.into_result(expr).map_err(RenamerError)
}

pub fn rename_module(module: Module<InternedStr>) -> Result<Module<Name>, RenamerError> {
    let mut renamer = Renamer::new();
    let m = rename_module_(&mut renamer, &[], module);
    renamer.errors.into_result(m).map_err(RenamerError)
}
fn rename_module_(
    renamer: &mut Renamer,
    module_env: &[Module<Name>],
    module: Module<InternedStr>,
) -> Module<Name> {
    let mut name = renamer.make_unique(module.name);
    if name.as_ref() == "Prelude" {
        renamer.uniques.find_mut(&name.name).unwrap().uid = 0;
        name.uid = 0;
    }
    renamer.uniques.enter_scope();
    renamer.insert_globals(module_env, &module, name.uid);
    let Module {
        name: _,
        imports,
        classes,
        data_definitions,
        newtypes,
        type_declarations,
        bindings,
        instances,
        fixity_declarations,
    } = module;

    let imports2: Vec<Import<Name>> = imports
        .into_iter()
        .map(|import| {
            let imports = import.imports.as_ref().map(|x| {
                let is: Vec<Name> = x.iter().map(|&x| renamer.get_name(x)).collect();
                is
            });
            Import {
                module: import.module,
                imports,
            }
        })
        .collect();

    let data_definitions2: Vec<DataDefinition<Name>> = data_definitions
        .into_iter()
        .map(|data| {
            let DataDefinition {
                constructors,
                typ,
                parameters,
                deriving,
            } = data;
            let c: Vec<Constructor<Name>> = constructors
                .into_iter()
                .map(|ctor| {
                    let Constructor {
                        name,
                        typ,
                        tag,
                        arity,
                    } = ctor;
                    Constructor {
                        name: renamer.get_name(name),
                        typ: renamer.rename_qualified_type(typ),
                        tag,
                        arity,
                    }
                })
                .collect();
            let d: Vec<Name> = deriving.into_iter().map(|s| renamer.get_name(s)).collect();

            DataDefinition {
                typ: renamer.rename_qualified_type(typ),
                parameters,
                constructors: c,
                deriving: d,
            }
        })
        .collect();

    let newtypes2: Vec<Newtype<Name>> = newtypes
        .into_iter()
        .map(|newtype| {
            let Newtype {
                typ,
                constructor_name,
                constructor_type,
                deriving,
            } = newtype;
            let deriving2: Vec<Name> = deriving.into_iter().map(|s| renamer.get_name(s)).collect();
            Newtype {
                typ,
                constructor_name: renamer.get_name(constructor_name),
                constructor_type: renamer.rename_qualified_type(constructor_type),
                deriving: deriving2,
            }
        })
        .collect();

    let instances2: Vec<Instance<Name>> = instances
        .into_iter()
        .map(|instance| {
            let Instance {
                bindings,
                constraints,
                typ,
                classname,
            } = instance;
            let constraints2: Vec<Constraint<Name>> = constraints
                .into_iter()
                .map(|Constraint { class, variables }| Constraint {
                    class: renamer.get_name(class),
                    variables,
                })
                .collect();
            Instance {
                bindings: renamer.rename_bindings(bindings, true),
                constraints: constraints2,
                typ: renamer.rename_type(typ),
                classname: renamer.get_name(classname),
            }
        })
        .collect();

    let classes2: Vec<Class<Name>> = classes
        .into_iter()
        .map(|class| {
            let Class {
                constraints,
                name,
                variable,
                declarations,
                bindings,
            } = class;
            let constraints2: Vec<Constraint<Name>> = constraints
                .into_iter()
                .map(|Constraint { class, variables }| Constraint {
                    class: renamer.get_name(class),
                    variables,
                })
                .collect();
            Class {
                constraints: constraints2,
                name: renamer.get_name(name),
                variable,
                declarations: renamer.rename_type_declarations(declarations),
                bindings: renamer.rename_bindings(bindings, true),
            }
        })
        .collect();

    let bindings2 = renamer.rename_bindings(bindings, true);

    let fixity_declarations2: Vec<FixityDeclaration<Name>> = fixity_declarations
        .into_iter()
        .map(
            |FixityDeclaration {
                 assoc,
                 precedence,
                 operators,
             }| {
                let ops: Vec<Name> = operators.into_iter().map(|s| renamer.get_name(s)).collect();
                FixityDeclaration {
                    assoc,
                    precedence,
                    operators: ops,
                }
            },
        )
        .collect();
    let decls2 = renamer.rename_type_declarations(type_declarations);
    renamer.uniques.exit_scope();
    Module {
        name,
        imports: imports2,
        classes: classes2,
        data_definitions: data_definitions2,
        type_declarations: decls2,
        bindings: bindings2,
        instances: instances2,
        newtypes: newtypes2,
        fixity_declarations: fixity_declarations2,
    }
}

pub fn prelude_name(s: &str) -> Name {
    Name {
        name: intern(s),
        uid: 0,
    }
}

///Renames a vector of modules.
///If any errors are encounterd while renaming, an error message is output and fail is called
pub fn rename_modules(
    modules: Vec<Module<InternedStr>>,
) -> Result<Vec<Module<Name>>, RenamerError> {
    let mut renamer = Renamer::new();
    let mut ms = vec![];
    for module in modules.into_iter() {
        let m = rename_module_(&mut renamer, ms.as_ref(), module);
        ms.push(m);
    }
    renamer.errors.into_result(ms).map_err(RenamerError)
}

pub mod typ {
    use super::{name, Name};
    use crate::interner::intern;
    use crate::types::{Kind, Type, TypeVariable};
    use std::iter::repeat;

    ///Constructs a string which holds the name of an n-tuple
    pub fn tuple_name(n: usize) -> String {
        let commas = if n == 0 { 0 } else { n - 1 };
        Some('(')
            .into_iter()
            .chain(repeat(',').take(commas))
            .chain(Some(')').into_iter())
            .collect()
    }
    ///Returns the type of an n-tuple constructor as well as the name of the tuple
    pub fn tuple_type(n: usize) -> (String, Type<Name>) {
        let mut var_list = vec![];
        assert!(n < 26);
        for i in 0..n {
            let c = (('a' as u8) + i as u8) as char;
            let var =
                TypeVariable::new_var_kind(intern(c.to_string().as_ref()), Kind::Star.clone());
            var_list.push(Type::Generic(var));
        }
        let ident = tuple_name(n);
        let mut typ = Type::new_op(name(ident.as_ref()), var_list);
        for i in (0..n).rev() {
            let c = (('a' as u8) + i as u8) as char;
            typ = function_type_(
                Type::Generic(TypeVariable::new(intern(c.to_string().as_ref()))),
                typ,
            );
        }
        (ident, typ)
    }

    ///Constructs a list type which holds elements of type 'typ'
    pub fn list_type(typ: Type<Name>) -> Type<Name> {
        Type::new_op(name("[]"), vec![typ])
    }
    ///Returns the Type of the Char type
    pub fn char_type() -> Type<Name> {
        Type::new_op(name("Char"), vec![])
    }
    ///Returns the type for the Int type
    pub fn int_type() -> Type<Name> {
        Type::new_op(name("Int"), vec![])
    }
    ///Returns the type for the Bool type
    pub fn bool_type() -> Type<Name> {
        Type::new_op(name("Bool"), vec![])
    }
    ///Returns the type for the Double type
    pub fn double_type() -> Type<Name> {
        Type::new_op(name("Double"), vec![])
    }
    ///Creates a function type
    pub fn function_type(arg: &Type<Name>, result: &Type<Name>) -> Type<Name> {
        function_type_(arg.clone(), result.clone())
    }

    ///Creates a function type
    pub fn function_type_(func: Type<Name>, arg: Type<Name>) -> Type<Name> {
        Type::new_op(name("->"), vec![func, arg])
    }

    ///Creates a IO type
    pub fn io(typ: Type<Name>) -> Type<Name> {
        Type::new_op(name("IO"), vec![typ])
    }
    ///Returns the unit type '()'
    pub fn unit() -> Type<Name> {
        Type::new_op(name("()"), vec![])
    }
}

#[cfg(test)]
pub mod tests {
    use super::Name;
    use crate::interner::InternedStr;
    use crate::module::{Module, TypedExpr};
    use crate::parser::*;

    pub fn rename_modules(modules: Vec<Module<InternedStr>>) -> Vec<Module<Name>> {
        super::rename_modules(modules).unwrap()
    }
    pub fn rename_module(module: Module<InternedStr>) -> Module<Name> {
        super::rename_module(module).unwrap()
    }
    pub fn rename_expr(expr: TypedExpr<InternedStr>) -> TypedExpr<Name> {
        super::rename_expr(expr).unwrap()
    }

    #[test]
    #[should_panic]
    fn duplicate_binding() {
        let mut parser = Parser::new(
            r"main = 1
test = []
main = 2"
                .chars(),
        );
        let module = parser.module().unwrap();
        rename_modules(vec![module]);
    }
    #[test]
    fn import_binding() {
        let file = r"
import Prelude (id)
main = id";
        let modules = parse_string(file).unwrap();
        rename_modules(modules);
    }
    #[test]
    #[should_panic]
    fn missing_import() {
        let mut parser = Parser::new(
            r"
import Prelude ()
main = id"
                .chars(),
        );
        let module = parser.module().unwrap();
        rename_modules(vec![module]);
    }
}
