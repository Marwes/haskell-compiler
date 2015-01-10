use std::mem::{swap};
use std::io::{IoResult, File};
use std::collections::{HashSet, HashMap};
use std::str::FromStr;
use lexer::*;
use lexer::TokenEnum::*;
use module::*;
use module::Expr::*;
use module::LiteralData::*;
use interner::*;

///The Parser is a recursive descent parser which has a method for each production
///in the AST. By calling such a production method it is expected that the parser is
///in a position where it starts at the first token of that production and can parse the production
///completely otherwise it will call fail with an appropriate error message.
///If the methods returns an Option it will instead return None.
///In any case it is expected that a production method will place the parser in a position where_bindings
///it can continue parsing without having to move the lexer's position.
pub struct Parser<Iter: Iterator<Item=char>> {
    lexer : Lexer<Iter>,
}

enum BindOrTypeDecl {
    Binding(Binding),
    TypeDecl(TypeDeclaration)
}


impl <Iter : Iterator<Item=char>> Parser<Iter> {

pub fn new(iterator : Iter) -> Parser<Iter> {
    Parser { lexer : Lexer::new(iterator) }
}

fn require_next<'a>(&'a mut self, expected : TokenEnum) -> &'a Token {
    let tok = if expected == RBRACE {
        self.lexer.next_end().token
    }
	else {
        self.lexer.next().token
    };
	if tok != expected {
		panic!(parse_error(&self.lexer, expected));
    }
	return self.lexer.current();
}

pub fn module(&mut self) -> Module {
	let lBracketOrModule = self.lexer.module_next().token;//tokenizeModule??
	let modulename = match lBracketOrModule {
        MODULE => {
            let modulename = self.require_next(NAME).value.clone();
            self.require_next(WHERE);
            self.require_next(LBRACE);
            modulename
	    }
        LBRACE => {
		    //No module declaration was found so default to Main
		    intern("Main")
	    }
        _ => panic!(parse_error(&self.lexer, LBRACE))
    };

    let mut imports = Vec::new();
    loop {
        if self.lexer.peek().token == IMPORT {
            imports.push(self.import());
            if self.lexer.peek().token == SEMICOLON {
                self.lexer.next();
            }
            else {
                break
            }
        }
        else {
            break
        }
    }

    let mut classes = Vec::new();
    let mut bindings = Vec::new();
    let mut instances = Vec::new();
    let mut type_declarations = Vec::new();
    let mut data_definitions = Vec::new();
    let mut newtypes = Vec::new();
    let mut fixity_declarations = Vec::new();
	loop {
		//Do a lookahead to see what the next top level binding is
		let token = self.lexer.peek().token;
		if token == NAME || token == LPARENS {
            match self.binding_or_type_declaration() {
                BindOrTypeDecl::Binding(bind) => bindings.push(bind),
                BindOrTypeDecl::TypeDecl(decl) => type_declarations.push(decl)
            }
		}
		else if token == CLASS {
			classes.push(self.class());
		}
		else if token == INSTANCE {
			instances.push(self.instance());
		}
		else if token == DATA {
			data_definitions.push(self.data_definition());
		}
		else if token == NEWTYPE {
			newtypes.push(self.newtype());
		}
		else if token == INFIXL || token == INFIXR || token == INFIX {
            fixity_declarations.push(self.fixity_declaration());
        }
        else {
            self.lexer.next();
			break;
		}
		let semicolon = self.lexer.next();
        debug!("More bindings? {:?}", semicolon.token);
	    if semicolon.token != SEMICOLON {
            break;
        }
    }

    self.lexer.backtrack();
    self.require_next(RBRACE);
    self.require_next(EOF);

    Module {
        name : modulename,
        imports : imports,
        bindings : bindings,
        type_declarations : type_declarations,
        classes : classes,
        instances : instances,
        data_definitions : data_definitions,
        newtypes: newtypes,
        fixity_declarations : fixity_declarations
    }
}

fn import(&mut self) -> Import<InternedStr> {
    self.require_next(IMPORT);
    let module_name = self.require_next(NAME).value;
    let imports = if self.lexer.peek().token == LPARENS {
        self.lexer.next();
        let x = if self.lexer.peek().token == RPARENS {
            self.lexer.next();
            Vec::new()
        }
        else {
            let imports = self.sep_by_1(|this| this.require_next(NAME).value, COMMA);
            self.require_next(RPARENS);
            imports
        };
        Some(x)
    }
    else {
        None
    };
    Import { module: module_name, imports: imports }
}

fn class(&mut self) -> Class {
	self.require_next(CLASS);
    let (constraints, typ) = self.constrained_type();

	self.require_next(WHERE);
	self.require_next(LBRACE);
	let x = self.sep_by_1(|this| this.binding_or_type_declaration(), SEMICOLON);
    let mut bindings = Vec::new();
    let mut declarations = Vec::new();
    for decl_or_binding in x.into_iter() {
        match decl_or_binding {
            BindOrTypeDecl::Binding(mut bind) => {
                //Bindings need to have their name altered to distinguish them from
                //the declarations name
                match typ {
                    Type::Application(ref op, _) => {
                        let classname = match **op {
                            Type::Constructor(ref ctor) => ctor.name,
                            _ => panic!("Expected type operator")
                        };
                        bind.name = encode_binding_identifier(classname, bind.name);
                    }
                    _ => panic!("The name of the class must start with an uppercase letter")
                }
                bindings.push(bind)
            }
            BindOrTypeDecl::TypeDecl(decl) => declarations.push(decl)
        }
    }
	
	self.require_next(RBRACE);

    match typ {
        Type::Application(box Type::Constructor(classname), box Type::Variable(var)) => {
            Class {
                constraints: constraints,
                name: classname.name,
                variable: var,
                declarations: declarations,
                bindings: bindings
            }
        }
        _ => panic!("Parse error in class declaration header")
    }
}

fn instance(&mut self) -> Instance {
	self.require_next(INSTANCE);

    let (constraints, instance_type) = self.constrained_type();
    match instance_type {
        Type::Application(op, arg) => {
            let classname = match *op {
                Type::Constructor(TypeConstructor { name: classname, ..}) => classname,
                _ => panic!("Expected type operator")
            };
            self.require_next(WHERE);
            self.require_next(LBRACE);

            let mut bindings = self.sep_by_1(|this| this.binding(), SEMICOLON);
            {
                let inner_type = extract_applied_type(&*arg);
                for bind in bindings.iter_mut() {
                    bind.name = encode_binding_identifier(inner_type.ctor().name, bind.name);
                }
            }

            self.require_next(RBRACE);
            Instance { typ : *arg, classname : classname, bindings : bindings, constraints: constraints }
        }
        _ => panic!("TypeVariable in instance")
    }
}

pub fn expression_(&mut self) -> TypedExpr {
    match self.expression() {
        Some(expr) => expr,
        None => panic!("Failed to parse expression at {:?}", self.lexer.current().location)
    }
}

pub fn expression(&mut self) -> Option<TypedExpr> {
	let app = self.application();
	self.binary_expression(app)
        .map(|expr| {
        //Try to parse a type signature on this expression
        if self.lexer.next().token == TYPEDECL {
            let (constraints, typ) = self.constrained_type();
            let loc = expr.location;
            TypedExpr::with_location(
                TypeSig(box expr, Qualified { constraints: constraints, value: typ }),
                loc)
        }
        else {
            self.lexer.backtrack();
            expr
        }
    })
}


fn list(&mut self) -> TypedExpr {
	let mut expressions = Vec::new();
	loop {
		match self.expression() {
            Some(expr) => expressions.push(expr),
            None => break
        }
		let comma = self.lexer.next().token;
        if comma != COMMA {
            self.lexer.backtrack();
            break;
        }
	}
    self.require_next(RBRACKET);

	let nil = TypedExpr::new(Identifier(intern("[]")));
    expressions.into_iter().rev().fold(nil, |application, expr| {
		let arguments = vec![expr, application];
		make_application(TypedExpr::new(Identifier(intern(":"))), arguments.into_iter())
	})
}

fn sub_expression(&mut self) -> Option<TypedExpr> {
	let token = self.lexer.next().token;
    debug!("Begin SubExpr {:?}", self.lexer.current());
	match token {
	    LPARENS => {
            let location = self.lexer.current().location;
            if self.lexer.peek().token == RPARENS {
                self.lexer.next();
                Some(TypedExpr::with_location(Identifier(intern("()")), location))
            }
            else {
                let mut expressions = self.sep_by_1(|this| this.expression_(), COMMA);
                self.require_next(RPARENS);
                if expressions.len() == 1 {
                    let expr = expressions.pop().unwrap();
                    let loc = expr.location;
                    Some(TypedExpr::with_location(Paren(box expr), loc))
                }
                else {
                    Some(new_tuple(expressions))
                }
            }
		}
	    LBRACKET => Some(self.list()),
	    LET => {
			let binds = self.let_bindings();

			let inToken = self.lexer.next().token;
			if inToken != IN {
				panic!(parse_error(&self.lexer, IN));
            }
			match self.expression() {
                Some(e) => {
                    Some(TypedExpr::new(Let(binds, box e)))
                }
                None => None
            }
		}
	    CASE => {
            let location = self.lexer.current().location;
			let expr = self.expression();

			self.require_next(OF);
			self.require_next(LBRACE);

			let alts = self.sep_by_1(|this| this.alternative(), SEMICOLON);
            self.require_next(RBRACE);
			match expr {
                Some(e) => Some(TypedExpr::with_location(Case(box e, alts), location)),
                None => None
            }
		}
        IF => {
            let location = self.lexer.current().location;
            let pred = self.expression_();
            if self.lexer.peek().token == SEMICOLON {
                self.lexer.next();
            }
            self.require_next(THEN);
            let if_true = self.expression_();
            if self.lexer.peek().token == SEMICOLON {
                self.lexer.next();
            }
            self.require_next(ELSE);
            let if_false = self.expression_();
            Some(TypedExpr::with_location(IfElse(box pred, box if_true, box if_false), location))
        }
        LAMBDA => {
            let args = self.pattern_arguments();
            self.require_next(ARROW);
            Some(make_lambda(args.into_iter(), self.expression_()))
        }
        DO => {
            let location = self.lexer.current().location;
            self.require_next(LBRACE);
            let bindings = self.sep_by_1(|this| this.do_binding(), SEMICOLON);
            self.require_next(RBRACE);
            if bindings.len() == 0 {
                panic!("{:?}: Parse error: Empty do", self.lexer.current().location);
            }
            let mut bs: Vec<DoBinding> = bindings.into_iter().collect();
            let expr = match bs.pop().unwrap() {
                DoBinding::DoExpr(e) => e,
                _ => panic!("{:?}: Parse error: Last binding in do must be an expression", self.lexer.current().location)
            };
            Some(TypedExpr::with_location(Do(bs, box expr), location))
        }
        NAME => {
            let token = self.lexer.current();
            Some(TypedExpr::with_location(Identifier(token.value.clone()), token.location))
        }
        NUMBER => {
            let token = self.lexer.current();
            Some(TypedExpr::with_location(Literal(Integral(FromStr::from_str(token.value.as_slice()).unwrap())), token.location))
        }
	    FLOAT => {
            let token = self.lexer.current();
            Some(TypedExpr::with_location(Literal(Fractional(FromStr::from_str(token.value.as_slice()).unwrap())), token.location))
        }
        STRING => {
            let token = self.lexer.current();
            Some(TypedExpr::with_location(Literal(String(token.value.clone())), token.location))
        }
        CHAR => {
            let token = self.lexer.current();
            Some(TypedExpr::with_location(Literal(Char(token.value.as_slice().char_at(0))), token.location))
        }
	    _ => {
            self.lexer.backtrack();
            None
        }
    }
}

fn do_binding(&mut self) -> DoBinding {
    if self.lexer.next().token == LET {
        return DoBinding::DoLet(self.let_bindings());
    }
    debug!("Do binding {:?}", self.lexer.current());
    self.lexer.backtrack();
    let mut lookahead = 0;
    loop {
        lookahead += 1;
        match self.lexer.next().token {
            SEMICOLON | RBRACE => {
                for _ in range(0, lookahead) { self.lexer.backtrack(); }
                return DoBinding::DoExpr(self.expression_());
            }
            LARROW => {
                for _ in range(0, lookahead) { self.lexer.backtrack(); }
                let p = self.located_pattern();
                self.lexer.next();//Skip <-
                return DoBinding::DoBind(p, self.expression_());
            }
            EOF => { panic!("Unexpected EOF") }
            _ => { debug!("Lookahead {:?}", self.lexer.current()); }
        }
    }
}

fn let_bindings(&mut self) -> Vec<Binding> {

    self.require_next(LBRACE);

    let binds = self.sep_by_1(|this| this.binding(), SEMICOLON);
    self.lexer.next_end();
    binds
}

fn alternative(&mut self) -> Alternative {
	let pat = self.located_pattern();

    let matches = self.expr_or_guards(ARROW);
    let where_bindings = if self.lexer.peek().token == WHERE {
        self.lexer.next();
        Some(self.let_bindings())
    }
    else {
        None
    };
	Alternative { pattern : pat, matches: matches, where_bindings: where_bindings }
}

fn binary_expression(&mut self, lhs : Option<TypedExpr>) -> Option<TypedExpr> {
    debug!("Parse operator expression, {:?}", self.lexer.current());
    if self.lexer.next().token == OPERATOR {
		let op = self.lexer.current().value;
        let loc = self.lexer.current().location;
		let rhs = self.application();
        let rhs = self.binary_expression(rhs);
        match (lhs, rhs) {
            (Some(lhs), Some(rhs)) => {
                Some(TypedExpr::with_location(OpApply(box lhs, op, box rhs), loc))
            }
            (Some(lhs), None) => {
		        let name = TypedExpr::with_location(Identifier(op), loc);
                Some(TypedExpr::with_location(Apply(box name, box lhs), loc))
            }
            (None, Some(rhs)) => {
                if op == intern("-") {
		            let name = TypedExpr::with_location(Identifier(intern("negate")), loc);
                    let args = vec![rhs];
                    Some(make_application(name, args.into_iter()))
                }
                else {
		            let name = TypedExpr::with_location(Identifier(intern("negate")), loc);
                    let args = vec![TypedExpr::with_location(Identifier(intern("#")), loc), rhs];
                    let mut apply = make_application(name, args.into_iter());
                    apply.location = loc;
                    let params = vec![intern("#")];
                    Some(make_lambda(params.into_iter().map(|a| Pattern::Identifier(a)), apply))
                }
            }
            (None, None) => return None
        }
	}
    else {
        self.lexer.backtrack();
        lhs
    }
}

fn application(&mut self) -> Option<TypedExpr> {
    let e = self.sub_expression();
	match e {
        Some(mut lhs) => {
            let mut expressions = Vec::new();
            loop {
                let expr = self.sub_expression();
                match expr {
                    Some(e) => expressions.push(e),
                    None => break
                }
            }
            if expressions.len() > 0 {
                let loc = lhs.location;
                lhs = make_application(lhs, expressions.into_iter());//, loc);
                lhs.location = loc;
            }
            Some(lhs)
        }
        None => None
    }
}

fn constructor(&mut self, dataDef : &DataDefinition) -> Constructor {
	let name = self.require_next(NAME).value.clone();
	let mut arity = 0;
	let typ = self.constructor_type(&mut arity, dataDef);
	self.lexer.backtrack();
	Constructor { name : name, typ : qualified(vec![], typ), tag : 0, arity : arity }
}

fn binding(&mut self) -> Binding {
    debug!("Begin binding");
	//name1 = expr
	//or
	//name2 x y = expr
	let nameToken = self.lexer.next().token;
	let mut name = self.lexer.current().value.clone();
	if nameToken == LPARENS {
		//Parse a name within parentheses
		let functionName = self.lexer.next().token;
		if functionName != NAME && functionName != OPERATOR {
			panic!("Expected NAME or OPERATOR on left side of binding {:?}", self.lexer.current().token);
		}
		name = self.lexer.current().value.clone();

		let rParens = self.lexer.next().token;
		if rParens != RPARENS {
			panic!(parse_error(&self.lexer, RPARENS));
		}
	}
	else if nameToken != NAME {
		panic!(parse_error(&self.lexer, NAME));
	}

	//Parse the arguments for the binding
	let arguments = self.pattern_arguments();
    let matches = self.expr_or_guards(EQUALSSIGN);
    let where_bindings = if self.lexer.peek().token == WHERE {
        self.lexer.next();
        Some(self.let_bindings())
    }
    else {
        None
    };
    Binding {
        name : name.clone(),
        typ: Default::default(),
        arguments: arguments,
        where_bindings : where_bindings,
        matches : matches,
    }
}

fn binding_or_type_declaration(&mut self) -> BindOrTypeDecl {
    //Since the token indicates an identifier it will be a function declaration or a function definition
    //We can disambiguate this by looking wether the '::' token appear.
    let token = self.lexer.next().token;
    let maybe_type_decl = if token == LPARENS {
        self.require_next(OPERATOR);
        self.require_next(RPARENS);
        let tok = self.lexer.next().token;
        self.lexer.backtrack();
        self.lexer.backtrack();
        self.lexer.backtrack();
        self.lexer.backtrack();
        tok
    }
    else {
        let tok = self.lexer.next().token;
        self.lexer.backtrack();
        self.lexer.backtrack();
        tok
    };

    if maybe_type_decl == TYPEDECL {
        BindOrTypeDecl::TypeDecl(self.type_declaration())
    }
    else {
        BindOrTypeDecl::Binding(self.binding())
    }
}

fn fixity_declaration(&mut self) -> FixityDeclaration {
    let assoc = {
        match self.lexer.next().token {
            INFIXL => Assoc::Left,
            INFIXR => Assoc::Right,
            INFIX => Assoc::No,
            _ => panic!(parse_error2(&self.lexer, &[INFIXL, INFIXR, INFIX]))
        }
    };
    let precedence = match self.lexer.next().token {
        NUMBER => FromStr::from_str(self.lexer.current().value.as_slice()).unwrap(),
        _ => {
            self.lexer.backtrack();
            9
        }
    };
    let operators = self.sep_by_1(|this| this.require_next(OPERATOR).value, COMMA);
    FixityDeclaration { assoc: assoc, precedence: precedence, operators: operators }
}

fn expr_or_guards(&mut self, end_token: TokenEnum) -> Match {
    let token = self.lexer.next().token;
    if token == PIPE {
        Match::Guards(self.sep_by_1(|this| this.guard(end_token), PIPE))
    }
    else if token == end_token {
        Match::Simple(self.expression_())
    }
    else {
        panic!(parse_error2(&self.lexer, &[end_token, PIPE]))
    }
}

fn guard(&mut self, end_token: TokenEnum) -> Guard {
    let p = self.expression_();
    self.require_next(end_token);
    Guard { predicate: p, expression: self.expression_() }
}

fn make_pattern<F>(&mut self, name: InternedStr, args: F) -> Pattern
    where F: FnOnce(&mut Parser<Iter>) -> Vec<Pattern> {
    let c = name.as_slice().char_at(0);
    if c.is_uppercase() || name == intern(":") {
        Pattern::Constructor(name, args(self))
    }
    else if c == '_' {
        Pattern::WildCard
    }
    else {
        Pattern::Identifier(name)
    }
}

fn pattern_arguments(&mut self) -> Vec<Pattern> {
	let mut parameters = Vec::new();
	loop {
		let token = self.lexer.next().token;
		match token {
            NAME => {
                let name = self.lexer.current().value;
                let p = self.make_pattern(name, |_| vec![]);
                parameters.push(p);
            }
            NUMBER => parameters.push(Pattern::Number(FromStr::from_str(self.lexer.current().value.as_slice()).unwrap())),
		    LPARENS => {
                self.lexer.backtrack();
				parameters.push(self.pattern());
			}
            LBRACKET => {
                if self.lexer.next().token != RBRACKET {
                    panic!(parse_error(&self.lexer, RBRACKET));
                }
                parameters.push(Pattern::Constructor(intern("[]"), vec![]));
            }
		    _ => { break; }
		}
	}
	self.lexer.backtrack();
	return parameters;
}

fn located_pattern(&mut self) -> Located<Pattern> {
    let location = self.lexer.next().location;
    self.lexer.backtrack();
    Located { location: location, node: self.pattern() }
}

fn pattern(&mut self) -> Pattern {
	let nameToken = self.lexer.next().token;
    let name = self.lexer.current().value.clone();
    let pat = match nameToken {
        LBRACKET => {
            if self.lexer.next().token != RBRACKET {
                panic!(parse_error(&self.lexer, RBRACKET));
            }
            Pattern::Constructor(intern("[]"), vec![])
        }
        NAME => self.make_pattern(name, |this| this.pattern_arguments()),
        NUMBER => Pattern::Number(FromStr::from_str(name.as_slice()).unwrap()),
        LPARENS => {
            if self.lexer.peek().token == RPARENS {
                self.lexer.next();
                Pattern::Constructor(intern("()"), vec![])
            }
            else {
                let mut tupleArgs = self.sep_by_1(|this| this.pattern(), COMMA);
                self.require_next(RPARENS);
                if tupleArgs.len() == 1 {
                    tupleArgs.pop().unwrap()
                }
                else {
                    Pattern::Constructor(intern(tuple_name(tupleArgs.len()).as_slice()), tupleArgs)
                }
            }
        }
        _ => { panic!("Error parsing pattern at token {:?}", self.lexer.current()) }
    };
    self.lexer.next();
    if self.lexer.current().token == OPERATOR && self.lexer.current().value.as_slice() == ":" {
        Pattern::Constructor(self.lexer.current().value, vec![pat, self.pattern()])
    }
    else {
        self.lexer.backtrack();
        pat
    }
}

fn type_declaration(&mut self) -> TypeDeclaration {
    let mut name;
	{
        let nameToken = self.lexer.next().token;
        name = self.lexer.current().value.clone();
        if nameToken == LPARENS {
            //Parse a name within parentheses
            let functionName = self.lexer.next().token;
            if functionName != NAME && functionName != OPERATOR {
                panic!("Expected NAME or OPERATOR on left side of binding {:?}", functionName);
            }
            name = self.lexer.current().value.clone();
            let rParens = self.lexer.next().token;
            if rParens != RPARENS {
                panic!(parse_error(&self.lexer, RPARENS));
            }
        }
        else if nameToken != NAME {
            panic!(parse_error(&self.lexer, NAME));
        }
    }
	let decl = self.lexer.next().token;
	if decl != TYPEDECL {
		panic!(parse_error(&self.lexer, TYPEDECL));
	}
    let (context, typ) = self.constrained_type();
	TypeDeclaration { name : name, typ : Qualified { constraints : context, value: typ } }
}

fn constrained_type(&mut self) -> (Vec<Constraint>, Type) {
    let mut maybeConstraints = if self.lexer.next().token == LPARENS {
        if self.lexer.peek().token == RPARENS {
            self.lexer.next();
            vec![]
        }
        else {
            let t = self.sep_by_1(|this| this.parse_type(), COMMA);
            self.require_next(RPARENS);
            t
        }
    }
    else {
        self.lexer.backtrack();
        vec![self.parse_type()]
    };
    let maybeContextArrow = self.lexer.next().token;
    //If there is => arrow we proceed to parse the type
    let typ = if maybeContextArrow == CONTEXTARROW {
        self.parse_type()
    }
    else if maybeContextArrow == ARROW {
	    self.lexer.backtrack();
        let mut args = Vec::new();
        swap(&mut args, &mut maybeConstraints);
        self.parse_return_type(make_tuple_type(args))
    }
    else {//If no => was found, translate the constraint list into a type
	    self.lexer.backtrack();
        let mut args = Vec::new();
        swap(&mut args, &mut maybeConstraints);
        make_tuple_type(args)
    };
	(make_constraints(maybeConstraints), typ)
}

fn constructor_type(&mut self, arity : &mut int, dataDef: &DataDefinition) -> Type {
	let token = self.lexer.next().token;
	if token == NAME {
		*arity += 1;
		let arg = if self.lexer.current().value.as_slice().char_at(0).is_lowercase() {
            Type::new_var(self.lexer.current().value)
		}
		else {
			Type::new_op(self.lexer.current().value.clone(), Vec::new())
        };
        function_type_(arg, self.constructor_type(arity, dataDef))
	}
	else if token == LPARENS {
        *arity += 1;
        let arg = self.parse_type();
        self.require_next(RPARENS);
        function_type_(arg, self.constructor_type(arity, dataDef))
    }
    else {
		dataDef.typ.value.clone()
	}
}


fn data_definition(&mut self) -> DataDefinition {
	self.require_next(DATA);

	let mut definition = DataDefinition {
        constructors : Vec::new(),
        typ : qualified(vec![], Type::new_var(intern("a"))),
        parameters : HashMap::new(),
        deriving: Vec::new()
    };
    definition.typ.value = self.data_lhs();
    self.require_next(EQUALSSIGN);

	definition.constructors = self.sep_by_1_func(|this| this.constructor(&definition),
		|t : &Token| t.token == PIPE);
	for ii in range(0, definition.constructors.len()) {
		definition.constructors[ii].tag = ii as int;
	}
    definition.deriving = self.deriving();
	definition
}

fn newtype(&mut self) -> Newtype {
    debug!("Parsing newtype");
    self.require_next(NEWTYPE);
    let typ = self.data_lhs();
    self.require_next(EQUALSSIGN);
    let name = self.require_next(NAME).value;
    let location = self.lexer.current().location;
    let arg_type = self.sub_type()
        .unwrap_or_else(|| panic!("Parse error when parsing argument to new type at  {:?}", location));
    
    Newtype {
        typ: qualified(Vec::new(), typ.clone()),
        constructor_name: name,
        constructor_type: qualified(Vec::new(), function_type_(arg_type, typ)),
        deriving: self.deriving()
    }
}

fn data_lhs(&mut self) -> Type {
	let name = self.require_next(NAME).value.clone();
    let mut typ = Type::Constructor(TypeConstructor { name: name, kind: star_kind.clone() });
	while self.lexer.next().token == NAME {
		typ = Type::Application(box typ, box Type::new_var(self.lexer.current().value));
	}
    self.lexer.backtrack();
    Parser::<Iter>::set_kind(&mut typ, 1);
    typ
}

fn deriving(&mut self) -> Vec<InternedStr> {
    if self.lexer.next().token == DERIVING {
        self.require_next(LPARENS);
        let vec = self.sep_by_1(|this| this.require_next(NAME).value, COMMA);
        self.require_next(RPARENS);
        vec
    }
    else {
	    self.lexer.backtrack();
        Vec::new()
    }
}

fn set_kind(typ: &mut Type, kind: int) {
    match typ {
        &mut Type::Application(ref mut lhs, _) => {
            Parser::<Iter>::set_kind(&mut **lhs, kind + 1)
        }
        _ => {
            *typ.mut_kind() = Kind::new(kind)
        }
    }
}

fn sub_type(&mut self) -> Option<Type> {
	let token = (*self.lexer.next()).clone();
	match token.token {
	    LBRACKET => {
            self.lexer.backtrack();
            Some(self.parse_type())
		}
	    LPARENS => {
            self.lexer.backtrack();
			Some(self.parse_type())
		}
	    NAME => {
			if token.value.as_slice().char_at(0).is_uppercase() {
				Some(Type::new_op(token.value, Vec::new()))
			}
			else {
				Some(Type::new_var(token.value))
			}
		}
        _ => { self.lexer.backtrack(); None }
	}
}

fn parse_type(&mut self) -> Type {
	let token = (*self.lexer.next()).clone();
	match token.token {
	    LBRACKET => {
            if self.lexer.next().token == RBRACKET {
                let listType = Type::new_op_kind(intern("[]"), vec![], Kind::new(2));
                self.parse_return_type(listType)
            }
            else {
                self.lexer.backtrack();
                let t = self.parse_type();
                self.require_next(RBRACKET);
                let listType = list_type(t);
                
                self.parse_return_type(listType)
            }
		}
	    LPARENS => {
            if self.lexer.peek().token == RPARENS {
                self.lexer.next();
                self.parse_return_type(Type::new_op(intern("()"), vec![]))
            }
            else {
                let t = self.parse_type();
                let maybeComma = self.lexer.next().token;
                if maybeComma == COMMA {
                    let mut tupleArgs: Vec<Type> = self.sep_by_1(|this| this.parse_type(), COMMA)
                        .into_iter()
                        .collect();
                    tupleArgs.insert(0, t);
                    self.require_next(RPARENS);

                    self.parse_return_type(make_tuple_type(tupleArgs))
                }
                else if maybeComma == RPARENS {
                    self.parse_return_type(t)
                }
                else {
                    panic!(parse_error2(&self.lexer, &[COMMA, RPARENS]))
                }
            }
		}
	    NAME => {
			let mut typeArguments = Vec::new();
            loop {
                match self.sub_type() {
                    Some(typ) => typeArguments.push(typ),
                    None => break
                }
            }

			let thisType = if token.value.as_slice().char_at(0).is_uppercase() {
				Type::new_op(token.value, typeArguments)
			}
			else {
                Type::new_var_args(token.value, typeArguments)
			};
			self.parse_return_type(thisType)
		}
	    _ => panic!("Unexpected token when parsing type {:?}", self.lexer.current())
	}
}

fn parse_return_type(&mut self, typ : Type) -> Type {
    let arrow = self.lexer.next().token;
    if arrow == ARROW {
        return function_type_(typ, self.parse_type());
    }
    else {
        self.lexer.backtrack();
        return typ
    }
}

fn sep_by_1<T, F>(&mut self, f : F, sep : TokenEnum) -> Vec<T>
    where F: FnMut(&mut Parser<Iter>) -> T {
    self.sep_by_1_func(f, |tok| tok.token == sep)
}

fn sep_by_1_func<T, F, P>(&mut self, mut f : F, mut sep: P) -> Vec<T>
    where F: FnMut(&mut Parser<Iter>) -> T, P : FnMut(&Token) -> bool {
    let mut result = Vec::new();
    loop {
        result.push(f(self));
        if !sep(self.lexer.next()) {
            self.lexer.backtrack();
            break;
        }
    }
    result
}
}//end impl Parser

fn make_constraints(types: Vec<Type>) -> Vec<Constraint> {
    types.into_iter().map(|typ| {
        match typ {
            Type::Application(lhs, rhs) => {
                Constraint { class: lhs.ctor().name.clone(), variables: vec![rhs.var().clone()] }
            }
            _ => panic!("Parse error in constraint, non applied type")
        }
    }).collect()
}

fn make_application<I: Iterator<Item=TypedExpr>>(f : TypedExpr, mut args : I) -> TypedExpr {
    let mut func = f;
	for a in args {
        let loc = func.location.clone();
		func = TypedExpr::with_location(Apply(box func, box a), loc);
	}
    func
}

fn make_lambda<Iter: DoubleEndedIterator<Item=Pattern<InternedStr>>>(args : Iter, body : TypedExpr) -> TypedExpr {
	let mut body = body;
	for a in args.rev() {
        let loc = body.location.clone();
		body = TypedExpr::with_location(Lambda(a, box body), loc);
	}
    body
}

//Create a tuple with the constructor name inferred from the number of arguments passed in
fn new_tuple(arguments : Vec<TypedExpr>) -> TypedExpr {
	let name = TypedExpr::new(Identifier(intern(tuple_name(arguments.len()).as_slice())));
	make_application(name, arguments.into_iter())
}

fn make_tuple_type(mut types : Vec<Type>) -> Type {
    if types.len() == 1 {
        types.pop().unwrap()
    }
    else {
	    Type::new_op(intern(tuple_name(types.len()).as_slice()), types)
    }
}

fn parse_error2<Iter : Iterator<Item=char>>(lexer : &Lexer<Iter>, expected : &[TokenEnum]) -> ::std::string::String {
    format!("Expected {:?} but found {:?}{{{:?}}}, at {:?}", expected, lexer.current().token, lexer.current().value.as_slice(), lexer.current().location)
    
}
fn parse_error<Iter : Iterator<Item=char>>(lexer : &Lexer<Iter>, expected : TokenEnum) -> ::std::string::String {
    format!("Expected {:?} but found {:?}{{{:?}}}, at {:?}", expected, lexer.current().token, lexer.current().value.as_slice(), lexer.current().location)
}

pub fn parse_string(contents: &str) -> IoResult<Vec<Module>> {
    let mut modules = Vec::new();
    let mut visited = HashSet::new();
    try!(parse_modules_(&mut visited, &mut modules, "<input>", contents));
    Ok(modules)
}

///Parses a module and all its imports
///If the modules contain a cyclic dependency fail is called.
pub fn parse_modules(modulename: &str) -> IoResult<Vec<Module>> {
    let mut modules = Vec::new();
    let mut visited = HashSet::new();
    let contents = try!(get_contents(modulename));
    try!(parse_modules_(&mut visited, &mut modules, modulename, contents.as_slice()));
    Ok(modules)
}

fn get_contents(modulename: &str) -> IoResult<::std::string::String> {
    let mut filename = ::std::string::String::from_str(modulename);
    filename.push_str(".hs");
    let mut file = File::open(&Path::new(filename.as_slice()));
    file.read_to_string()
}

fn parse_modules_(visited: &mut HashSet<InternedStr>, modules: &mut Vec<Module>, modulename: &str, contents: &str) -> IoResult<()> {
    let mut parser = Parser::new(contents.as_slice().chars());
    let module = parser.module();
    let interned_name = intern(modulename);
    visited.insert(interned_name);
    for import in module.imports.iter() {
        if visited.contains(&import.module) {
            panic!("Cyclic dependency in modules");
        }
        else if modules.iter().all(|m| m.name != import.module) {
            //parse the module if it is not parsed
            let import_module = import.module.as_slice();
            let contents_next = try!(get_contents(import_module));
            try!(parse_modules_(visited, modules, import_module, contents_next.as_slice()));
        }
    }
    visited.remove(&interned_name);
    modules.push(module);
    Ok(())
}

#[cfg(test)]
mod tests {

use interner::*;
use lexer::{Location, Located };
use parser::*;
use module::*;
use module::Expr::*;
use typecheck::{identifier, apply, op_apply, number, rational, lambda, let_, case, if_else};
use std::io::File;
use test::Bencher;


#[test]
fn simple()
{
    let mut parser = Parser::new("2 + 3".chars());
    let expr = parser.expression_();
    assert_eq!(expr, op_apply(number(2), intern("+"), number(3)));
}
#[test]
fn binding()
{
    let mut parser = Parser::new("test x = x + 3".chars());
    let bind = parser.binding();
    assert_eq!(bind.arguments, vec![Pattern::Identifier(intern("x"))]);
    assert_eq!(bind.matches, Match::Simple(op_apply(identifier("x"), intern("+"), number(3))));
    assert_eq!(bind.name, intern("test"));
}

#[test]
fn double()
{
    let mut parser = Parser::new("test = 3.14".chars());
    let bind = parser.binding();
    assert_eq!(bind.matches, Match::Simple(rational(3.14)));
    assert_eq!(bind.name, intern("test"));
}

#[test]
fn parse_let() {
    let mut parser = Parser::new(
r"
let
    test = add 3 2
in test - 2".chars());
    let expr = parser.expression_();
    let bind = Binding { arguments: vec![], name: intern("test"), typ: Default::default(),
        matches: Match::Simple(apply(apply(identifier("add"), number(3)), number(2))), where_bindings: None };
    assert_eq!(expr, let_(vec![bind], op_apply(identifier("test"), intern("-"), number(2))));
}

#[test]
fn parse_case() {
    let mut parser = Parser::new(
r"case [] of
    x:xs -> x
    [] -> 2
".chars());
    let expression = parser.expression_();
    let alt = Alternative {
        pattern: Located {
            location: Location::eof(),
            node: Pattern::Constructor(intern(":"), vec![Pattern::Identifier(intern("x")), Pattern::Identifier(intern("xs"))])
        },
        matches: Match::Simple(identifier("x")),
        where_bindings: None
    };
    let alt2 = Alternative {
        pattern: Located { location: Location::eof(), node: Pattern::Constructor(intern("[]"), vec![]) },
        matches: Match::Simple(number(2)),
        where_bindings: None
    };
    assert_eq!(expression, case(identifier("[]"), vec![alt, alt2]));
}

#[test]
fn parse_type() {
    let mut parser = Parser::new(
r"(.) :: (b -> c) -> (a -> b) -> (a -> c)".chars());
    let typeDecl = parser.type_declaration();
    let a = &Type::new_var(intern("a"));
    let b = &Type::new_var(intern("b"));
    let c = &Type::new_var(intern("c"));
    let f = function_type(&function_type(b, c), &function_type(&function_type(a, b), &function_type(a, c)));

    assert_eq!(typeDecl.name, intern("."));
    assert_eq!(typeDecl.typ.value, f);
}
#[test]
fn parse_data() {
    let mut parser = Parser::new(
r"data Bool = True | False".chars());
    let data = parser.data_definition();

    let b = qualified(vec![], bool_type());
    let t = Constructor { name: intern("True"), tag:0, arity:0, typ: b.clone() };
    let f = Constructor { name: intern("False"), tag:1, arity:0, typ: b.clone() };
    assert_eq!(data.typ, b);
    assert_eq!(data.constructors[0], t);
    assert_eq!(data.constructors[1], f);
}

#[test]
fn parse_data_2() {
    let mut parser = Parser::new(
r"data List a = Cons a (List a) | Nil".chars());
    let data = parser.data_definition();

    let list = Type::new_op(intern("List"), vec![Type::new_var(intern("a"))]);
    let cons = Constructor { name: intern("Cons"), tag:0, arity:2, typ: qualified(vec![], function_type(&Type::new_var(intern("a")), &function_type(&list, &list))) };
    let nil = Constructor { name: intern("Nil"), tag:1, arity:0, typ: qualified(vec![], list.clone()) };
    assert_eq!(data.typ.value, list);
    assert_eq!(data.constructors[0], cons);
    assert_eq!(data.constructors[1], nil);
}

#[test]
fn parse_tuple() {
    let mut parser = Parser::new(
r"(1, x)".chars());
    let expr = parser.expression_();

    assert_eq!(expr, apply(apply(identifier("(,)"), number(1)), identifier("x")));
}

#[test]
fn parse_unit() {
    let mut parser = Parser::new(
r"case () :: () of
    () -> 1".chars());
    let expr = parser.expression_();

    assert_eq!(expr, case(TypedExpr::new(TypeSig(box identifier("()"), qualified(vec![], Type::new_op(intern("()"), vec![])))), 
        vec![Alternative {
        pattern: Located { location: Location::eof(), node: Pattern::Constructor(intern("()"), vec![])  },
        matches: Match::Simple(number(1)),
        where_bindings: None
    } ]));
}

#[test]
fn test_operators() {
    let mut parser = Parser::new("1 : 2 : []".chars());
    let expr = parser.expression_();
    assert_eq!(expr, op_apply(number(1), intern(":"), op_apply(number(2), intern(":"), identifier("[]"))));
}

#[test]
fn parse_instance_class() {
    let mut parser = Parser::new(
r"class Eq a where_bindings
    (==) :: a -> a -> Bool
    (/=) x y = not (x == y)
    (/=) :: a -> a -> Bool


instance Eq a => Eq [a] where_bindings
    (==) xs ys = undefined".chars());
    let module = parser.module();

    assert_eq!(module.classes[0].name, intern("Eq"));
    assert_eq!(module.classes[0].bindings[0].name, intern("#Eq/="));
    assert_eq!(module.classes[0].bindings.len(), 1);
    assert_eq!(module.classes[0].declarations[0].name, intern("=="));
    assert_eq!(module.classes[0].declarations[1].name, intern("/="));
    assert_eq!(module.instances[0].classname, intern("Eq"));
    assert_eq!(module.instances[0].constraints[0].class, intern("Eq"));
    assert_eq!(module.instances[0].typ, list_type(Type::new_var(intern("a"))));
}
#[test]
fn parse_super_class() {
    let mut parser = Parser::new(
r"class Eq a => Ord a where_bindings
    (<) :: a -> a -> Bool

".chars());
    let module = parser.module();

    let cls = &module.classes[0];
    let a = Type::new_var(intern("a")).var().clone();
    assert_eq!(cls.name, intern("Ord"));
    assert_eq!(cls.variable, a);
    assert_eq!(cls.constraints[0].class, intern("Eq"));
    assert_eq!(cls.constraints[0].variables[0], a);
}
#[test]
fn parse_do_expr() {
    let mut parser = Parser::new(
r"main = do
    putStrLn test
    s <- getContents
    return s
".chars());
    let module = parser.module();

    let b = TypedExpr::new(Do(vec![
        DoBinding::DoExpr(apply(identifier("putStrLn"), identifier("test"))),
        DoBinding::DoBind(Located { location: Location::eof(), node: Pattern::Identifier(intern("s")) }, identifier("getContents"))
        ], box apply(identifier("return"), identifier("s"))));
    assert_eq!(module.bindings[0].matches, Match::Simple(b));
}
#[test]
fn lambda_pattern() {
    let mut parser = Parser::new(r"\(x, _) -> x".chars());
    let expr = parser.expression_();
    let pattern = Pattern::Constructor(intern("(,)"), vec![Pattern::Identifier(intern("x")), Pattern::WildCard]);
    assert_eq!(expr, TypedExpr::new(Lambda(pattern, box identifier("x"))));
}


#[test]
fn parse_imports() {
    let mut parser = Parser::new(
r"import Hello
import World ()
import Prelude (id, sum)

".chars());
    let module = parser.module();

    assert_eq!(module.imports[0].module.as_slice(), "Hello");
    assert_eq!(module.imports[0].imports, None);
    assert_eq!(module.imports[1].module.as_slice(), "World");
    assert_eq!(module.imports[1].imports, Some(Vec::new()));
    assert_eq!(module.imports[2].module.as_slice(), "Prelude");
    assert_eq!(module.imports[2].imports, Some(vec![intern("id"), intern("sum")]));
}
#[test]
fn parse_module_imports() {
    let modules = parse_modules("Test").unwrap();

    assert_eq!(modules[0].name.as_slice(), "Prelude");
    assert_eq!(modules[1].name.as_slice(), "Test");
    assert_eq!(modules[1].imports[0].module.as_slice(), "Prelude");
}

#[test]
fn parse_guards() {
    let mut parser = Parser::new(
r"
test x
    | x = 1
    | otherwise = 0
".chars());
    let binding = parser.binding();
    let b2 = Binding { arguments: vec![Pattern::Identifier(intern("x"))], name: intern("test"), typ: Default::default(),
        matches: Match::Guards(vec![
            Guard { predicate: identifier("x"), expression: number(1) },
            Guard { predicate: identifier("otherwise"), expression: number(0) },
        ]),
        where_bindings: None
    };
    assert_eq!(binding, b2);
}

#[test]
fn parse_fixity() {
    let mut parser = Parser::new(
r"
test x y = 2

infixr 5 `test`

infixr 6 `test2`, |<

test2 x y = 1
".chars());
    let module = parser.module();
    assert_eq!(module.fixity_declarations, [
        FixityDeclaration { assoc: Assoc::Right, precedence: 5, operators: vec![intern("test")] },
        FixityDeclaration { assoc: Assoc::Right, precedence: 6, operators: vec![intern("test2"), intern("|<")] },
    ]);
}

#[test]
fn deriving() {
    let mut parser = Parser::new(
r"data Test = A | B
    deriving(Eq, Show)

dummy = 1
".chars());
    let module = parser.module();
    let data = &module.data_definitions[0];
    assert_eq!(data.typ, qualified(Vec::new(), Type::new_op(intern("Test"), Vec::new())));
    assert_eq!(data.deriving, [intern("Eq"), intern("Show")]);
}

#[test]
fn test_if_else() {
    let mut parser = Parser::new(
r"
if test 1 
    then 1
    else if True
        then 2
        else 3 + 2
".chars());
    let e = parser.expression_();
    assert_eq!(e,
        if_else(apply(identifier("test"), number(1))
            , number(1)
            , if_else(identifier("True")
                , number(2)
                , op_apply(number(3), intern("+"), number(2)))));
}

#[test]
fn where_bindings() {
    let mut parser = Parser::new(
r"
test = case a of
        x:y:xs -> z
            where_bindings
            z = x + y
        x:xs -> x
        [] -> z
            where_bindings z = 0
    where_bindings
        a = []
".chars());
    let bind = parser.binding();
    match bind.matches {
        Match::Simple(ref e) => {
            match e.expr {
                Case(_, ref alts) => {
                    let w = alts[0].where_bindings.as_ref().expect("Expected where_bindings");
                    assert_eq!(w[0].name, intern("z"));
                    assert_eq!(w[0].matches, Match::Simple(op_apply(identifier("x"), intern("+"), identifier("y"))));
                    let w2 = alts[2].where_bindings.as_ref().expect("Expected where_bindings");
                    assert_eq!(w2[0].name, intern("z"));
                    assert_eq!(w2[0].matches, Match::Simple(number(0)));
                }
                _ => panic!("Expected case")
            }
        }
        _ => panic!("Expected simple binding")
    }
    let binds = bind.where_bindings.as_ref().expect("Expected where_bindings");
    assert_eq!(binds[0].name, intern("a"));
    assert_eq!(binds[0].matches, Match::Simple(identifier("[]")));
}

#[test]
fn parse_newtype() {
    let s = 
r"
newtype IntPair a = IntPair (a, Int)
";
    let module = Parser::new(s.chars()).module();
    let a = Type::new_var(intern("a"));
    let typ = Type::new_op(intern("IntPair"), vec![a.clone()]);
    assert_eq!(module.newtypes[0].typ, qualified(Vec::new(), typ.clone()));
    assert_eq!(module.newtypes[0].constructor_type.value, function_type_(Type::new_op(intern("(,)"), vec![a, int_type()]), typ));
}

#[test]
fn parse_prelude() {
    let path = &Path::new("Prelude.hs");
    let contents  = File::open(path).read_to_string().unwrap();
    let mut parser = Parser::new(contents.as_slice().chars());
    let module = parser.module();

    assert!(module.bindings.iter().any(|bind| bind.name == intern("foldl")));
    assert!(module.bindings.iter().any(|bind| bind.name == intern("id")));
    assert!(module.classes.iter().any(|class| class.name == intern("Eq")));
}

#[bench]
fn bench_prelude(b: &mut Bencher) {
    let path = &Path::new("Prelude.hs");
    let contents  = File::open(path).read_to_string().unwrap();
    b.iter(|| {
        let mut parser = Parser::new(contents.as_slice().chars());
        parser.module();
    });
}

}
