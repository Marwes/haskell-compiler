use std::mem::{swap};
use std::vec::FromVec;
use std::io::{IoResult, File};
use collections::{HashSet, HashMap};
use lexer::*;
use module::*;
use interner::*;

///The Parser is a recursive descent parser which has a method for each production
///in the AST. By calling such a production method it is expected that the parser is
///in a position where it starts at the first token of that production and can parse the production
///completely otherwise it will call fail with an appropriate error message.
///If the methods returns an Option it will instead return None.
///In any case it is expected that a production method will place the parser in a position where
///it can continue parsing without having to move the lexer's position.
pub struct Parser<Iter> {
    lexer : Lexer<Iter>,
}

enum BindOrTypeDecl {
    Binding(Binding),
    TypeDecl(TypeDeclaration)
}


impl <Iter : Iterator<char>> Parser<Iter> {

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
		fail!(parse_error(&self.lexer, expected));
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
        _ => fail!(parse_error(&self.lexer, LBRACE))
    };

    let mut imports = Vec::new();
    loop {
        if self.lexer.next().token == IMPORT {
            self.lexer.backtrack();
            imports.push(self.import());
            if self.lexer.next().token != SEMICOLON {
                break;
            }
        }
        else {
            self.lexer.backtrack();
            break;
        }
    }

    let mut classes = Vec::new();
    let mut bindings = Vec::new();
    let mut instances = Vec::new();
    let mut type_declarations = Vec::new();
    let mut data_definitions = Vec::new();
    let mut fixity_declarations = Vec::new();
	loop {
		//Do a lookahead to see what the next top level binding is
		let token = self.lexer.peek().token;
		if token == NAME || token == LPARENS {
            match self.binding_or_type_declaration() {
                Binding(bind) => bindings.push(bind),
                TypeDecl(decl) => type_declarations.push(decl)
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
		else if token == INFIXL || token == INFIXR || token == INFIX {
            fixity_declarations.push(self.fixity_declaration());
        }
        else {
            self.lexer.next();
			break;
		}
		let semicolon = self.lexer.next();
        debug!("More bindings? {}", semicolon.token);
	    if semicolon.token != SEMICOLON {
            break;
        }
    }

    self.lexer.backtrack();
    self.require_next(RBRACE);
    self.require_next(EOF);

    Module {
        name : modulename,
        imports : FromVec::from_vec(imports),
        bindings : FromVec::from_vec(bindings),
        typeDeclarations : FromVec::from_vec(type_declarations),
        classes : FromVec::from_vec(classes),
        instances : FromVec::from_vec(instances),
        dataDefinitions : FromVec::from_vec(data_definitions),
        fixity_declarations : FromVec::from_vec(fixity_declarations)
    }
}

fn import(&mut self) -> Import {
    self.require_next(IMPORT);
    let tok = self.require_next(NAME);
    Import { module: tok.value }
}

fn class(&mut self) -> Class {
	self.require_next(CLASS);
    let (constraints, typ) = self.constrained_type();

	self.require_next(WHERE);
	self.require_next(LBRACE);
	let x = self.sep_by_1(|this| this.binding_or_type_declaration(), SEMICOLON);
    let mut bindings = Vec::new();
    let mut declarations = Vec::new();
    for decl_or_binding in x.move_iter() {
        match decl_or_binding {
            Binding(mut bind) => {
                //Bindings need to have their name altered to distinguish them from
                //the declarations name
                match typ {
                    TypeApplication(ref op, _) => {
                        let classname = match **op {
                            TypeConstructor(ref ctor) => ctor.name,
                            _ => fail!("Expected type operator")
                        };
                        bind.name = encode_binding_identifier(classname, bind.name);
                    }
                    _ => fail!("The name of the class must start with an uppercase letter")
                }
                bindings.push(bind)
            }
            TypeDecl(decl) => declarations.push(decl)
        }
    }
	
	self.lexer.backtrack();
	self.require_next(RBRACE);

    match typ {
        TypeApplication(box TypeConstructor(classname), box TypeVariable(var)) => {
            Class {
                constraints: constraints,
                name: classname.name,
                variable: var,
                declarations: FromVec::from_vec(declarations),
                bindings: FromVec::from_vec(bindings)
            }
        }
        _ => fail!("Parse error in class declaration header")
    }
}

fn instance(&mut self) -> Instance {
	self.require_next(INSTANCE);

    let (constraints, instance_type) = self.constrained_type();
    match instance_type {
        TypeApplication(op, arg) => {
            let classname = match *op {
                TypeConstructor(TypeConstructor { name: classname, ..}) => classname,
                _ => fail!("Expected type operator")
            };
            self.require_next(WHERE);
            self.require_next(LBRACE);

            let mut bindings = self.sep_by_1(|this| this.binding(), SEMICOLON);
            {
                let inner_type = extract_applied_type(arg);
                for bind in bindings.mut_iter() {
                    bind.name = encode_binding_identifier(inner_type.ctor().name, bind.name);
                }
            }

            self.lexer.backtrack();
            self.require_next(RBRACE);
            Instance { typ : *arg, classname : classname, bindings : bindings, constraints: constraints }
        }
        _ => fail!("TypeVariable in instance")
    }
}

pub fn expression_(&mut self) -> TypedExpr {
    match self.expression() {
        Some(expr) => expr,
        None => fail!("Failed to parse expression at {}", self.lexer.current().location)
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
    expressions.move_iter().rev().fold(nil, |application, expr| {
		let arguments = ~[expr, application];
		make_application(TypedExpr::new(Identifier(intern(":"))), arguments.move_iter())
	})
}

fn sub_expression(&mut self) -> Option<TypedExpr> {
	let token = self.lexer.next().token;
    debug!("Begin SubExpr {}", self.lexer.current());
	match token {
	    LPARENS => {
            let location = self.lexer.current().location;
            if self.lexer.peek().token == RPARENS {
                self.lexer.next();
                Some(TypedExpr::with_location(Identifier(intern("()")), location))
            }
            else {
                let expressions = self.sep_by_1(|this| this.expression_(), COMMA);

                let maybeParens = self.lexer.current();

                if maybeParens.token != RPARENS {
                    fail!(parse_error(&self.lexer, RPARENS));
                }
                if expressions.len() == 1 {
                    let loc = expressions[0].location;
                    Some(TypedExpr::with_location(Paren(box expressions[0]), loc))
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
				fail!(parse_error(&self.lexer, IN));
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
            self.lexer.backtrack();
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
            Some(make_lambda(args.move_iter(), self.expression_()))
        }
        DO => {
            let location = self.lexer.current().location;
            self.require_next(LBRACE);
            let bindings = self.sep_by_1(|this| this.do_binding(), SEMICOLON);
            self.lexer.backtrack();
            self.require_next(RBRACE);
            if bindings.len() == 0 {
                fail!("{}: Parse error: Empty do", self.lexer.current().location);
            }
            let mut bs: Vec<DoBinding> = bindings.move_iter().collect();
            let expr = match bs.pop().unwrap() {
                DoExpr(e) => e,
                _ => fail!("{}: Parse error: Last binding in do must be an expression", self.lexer.current().location)
            };
            Some(TypedExpr::with_location(Do(FromVec::from_vec(bs), box expr), location))
        }
        NAME => {
            let token = self.lexer.current();
            Some(TypedExpr::with_location(Identifier(token.value.clone()), token.location))
        }
        NUMBER => {
            let token = self.lexer.current();
            Some(TypedExpr::with_location(Literal(Integral(from_str(token.value.as_slice()).unwrap())), token.location))
        }
	    FLOAT => {
            let token = self.lexer.current();
            Some(TypedExpr::with_location(Literal(Fractional(from_str(token.value.as_slice()).unwrap())), token.location))
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
        return DoLet(self.let_bindings());
    }
    debug!("Do binding {}", self.lexer.current());
    self.lexer.backtrack();
    let mut lookahead = 0;
    loop {
        lookahead += 1;
        match self.lexer.next().token {
            SEMICOLON | RBRACE => {
                for _ in range(0, lookahead) { self.lexer.backtrack(); }
                return DoExpr(self.expression_());
            }
            LARROW => {
                for _ in range(0, lookahead) { self.lexer.backtrack(); }
                let p = self.located_pattern();
                self.lexer.next();//Skip <-
                return DoBind(p, self.expression_());
            }
            EOF => { fail!("Unexpected EOF") }
            _ => { debug!("Lookahead {}", self.lexer.current()); }
        }
    }
}

fn let_bindings(&mut self) -> ~[Binding] {

    self.require_next(LBRACE);

    let binds = self.sep_by_1(|this| this.binding(), SEMICOLON);
    self.lexer.backtrack();
    self.lexer.next_end();
    binds
}

fn alternative(&mut self) -> Alternative {
	let pat = self.located_pattern();

    let matches = self.expr_or_guards(ARROW);
	Alternative { pattern : pat, matches: matches, where: None }
}

fn binary_expression(&mut self, lhs : Option<TypedExpr>) -> Option<TypedExpr> {
    debug!("Parse operator expression, {}", self.lexer.current());
    if self.lexer.next().token == OPERATOR {
		let op = self.lexer.current().value;
        let op_location = self.lexer.current().location;
		let rhs = self.application();
        let rhs = self.binary_expression(rhs);
		let loc = match lhs {
            Some(ref l) => l.location,
            None => op_location
        };
        match (lhs, rhs) {
            (Some(lhs), Some(rhs)) => {
                Some(TypedExpr::with_location(OpApply(box lhs, op, box rhs), loc))
            }
            (Some(lhs), None) => {
		        let name = TypedExpr::with_location(Identifier(op), op_location);
                Some(TypedExpr::with_location(Apply(box name, box lhs), loc))
            }
            (None, Some(rhs)) => {
                if op == intern("-") {
		            let name = TypedExpr::with_location(Identifier(intern("negate")), loc);
                    let args = ~[rhs];
                    Some(make_application(name, args.move_iter()))
                }
                else {
		            let name = TypedExpr::with_location(Identifier(intern("negate")), loc);
                    let args = ~[TypedExpr::with_location(Identifier(intern("#")), loc), rhs];
                    let mut apply = make_application(name, args.move_iter());
                    apply.location = loc;
                    let params = ~[intern("#")];
                    Some(make_lambda(params.move_iter().map(|a| IdentifierPattern(a)), apply))
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
                lhs = make_application(lhs, expressions.move_iter());//, loc);
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
	Constructor { name : name, typ : qualified(~[], typ), tag : 0, arity : arity }
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
			fail!("Expected NAME or OPERATOR on left side of binding {}", self.lexer.current().token);
		}
		name = self.lexer.current().value.clone();

		let rParens = self.lexer.next().token;
		if rParens != RPARENS {
			fail!(parse_error(&self.lexer, RPARENS));
		}
	}
	else if nameToken != NAME {
		fail!(parse_error(&self.lexer, NAME));
	}

	//Parse the arguments for the binding
	let arguments = self.pattern_arguments();
    let matches = self.expr_or_guards(EQUALSSIGN);
    Binding {
        name : name.clone(),
        typ: Default::default(),
        arguments: arguments,
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
        TypeDecl(self.type_declaration())
    }
    else {
        Binding(self.binding())
    }
}

fn fixity_declaration(&mut self) -> FixityDeclaration {
    let assoc = {
        match self.lexer.next().token {
            INFIXL => LeftAssoc,
            INFIXR => RightAssoc,
            INFIX => NoAssoc,
            _ => fail!(parse_error2(&self.lexer, [INFIXL, INFIXR, INFIX]))
        }
    };
    let precedence = match self.lexer.next().token {
        NUMBER => from_str(self.lexer.current().value.as_slice()).unwrap(),
        _ => {
            self.lexer.backtrack();
            9
        }
    };
    let operators = self.sep_by_1(|this| this.require_next(OPERATOR).value, COMMA);
    self.lexer.backtrack();
    FixityDeclaration { assoc: assoc, precedence: precedence, operators: operators }
}

fn expr_or_guards(&mut self, end_token: TokenEnum) -> Match {
    let token = self.lexer.next().token;
    if token == PIPE {
        let g = Guards(self.sep_by_1(|this| this.guard(end_token), PIPE));
        self.lexer.backtrack();
        g
    }
    else if token == end_token {
        Simple(self.expression_())
    }
    else {
        fail!(parse_error2(&self.lexer, [end_token, PIPE]))
    }
}

fn guard(&mut self, end_token: TokenEnum) -> Guard {
    let p = self.expression_();
    self.require_next(end_token);
    Guard { predicate: p, expression: self.expression_() }
}

fn make_pattern(&mut self, name: InternedStr, args: |&mut Parser<Iter>| -> ~[Pattern]) -> Pattern {
    let c = name.as_slice().char_at(0);
    if c.is_uppercase() || name == intern(":") {
        ConstructorPattern(name, args(self))
    }
    else if c == '_' {
        WildCardPattern
    }
    else {
        IdentifierPattern(name)
    }
}

fn pattern_arguments(&mut self) -> ~[Pattern] {
	let mut parameters = Vec::new();
	loop {
		let token = self.lexer.next().token;
		match token {
            NAME => {
                let name = self.lexer.current().value;
                let p = self.make_pattern(name, |_| ~[]);
                parameters.push(p);
            }
            NUMBER => parameters.push(NumberPattern(from_str(self.lexer.current().value.as_slice()).unwrap())),
		    LPARENS => {
                self.lexer.backtrack();
				parameters.push(self.pattern());
			}
            LBRACKET => {
                if self.lexer.next().token != RBRACKET {
                    fail!(parse_error(&self.lexer, RBRACKET));
                }
                parameters.push(ConstructorPattern(intern("[]"), ~[]));
            }
		    _ => { break; }
		}
	}
	self.lexer.backtrack();
	return FromVec::from_vec(parameters);
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
                fail!(parse_error(&self.lexer, RBRACKET));
            }
            ConstructorPattern(intern("[]"), ~[])
        }
        NAME => self.make_pattern(name, |this| this.pattern_arguments()),
        NUMBER => NumberPattern(from_str(name.as_slice()).unwrap()),
        LPARENS => {
            if self.lexer.peek().token == RPARENS {
                self.lexer.next();
                ConstructorPattern(intern("()"), ~[])
            }
            else {
                let tupleArgs = self.sep_by_1(|this| this.pattern(), COMMA);
                let rParens = self.lexer.current().token;
                if rParens != RPARENS {
                    fail!(parse_error(&self.lexer, RPARENS));
                }
                if tupleArgs.len() == 1 {
                    tupleArgs[0]
                }
                else {
                    ConstructorPattern(intern(tuple_name(tupleArgs.len()).as_slice()), tupleArgs)
                }
            }
        }
        _ => { fail!("Error parsing pattern at token {}", self.lexer.current()) }
    };
    self.lexer.next();
    if self.lexer.current().token == OPERATOR && self.lexer.current().value.as_slice() == ":" {
        ConstructorPattern(self.lexer.current().value, ~[pat, self.pattern()])
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
                fail!("Expected NAME or OPERATOR on left side of binding {}", functionName);
            }
            name = self.lexer.current().value.clone();
            let rParens = self.lexer.next().token;
            if rParens != RPARENS {
                fail!(parse_error(&self.lexer, RPARENS));
            }
        }
        else if nameToken != NAME {
            fail!(parse_error(&self.lexer, NAME));
        }
    }
	let decl = self.lexer.next().token;
	if decl != TYPEDECL {
		fail!(parse_error(&self.lexer, TYPEDECL));
	}
    let (context, typ) = self.constrained_type();
	TypeDeclaration { name : name, typ : Qualified { constraints : context, value: typ } }
}

fn constrained_type(&mut self) -> (~[Constraint], Type) {
    let mut maybeConstraints = if self.lexer.next().token == LPARENS {
        if self.lexer.peek().token == RPARENS {
            self.lexer.next();
            ~[]
        }
        else {
            let t = self.sep_by_1(|this| this.parse_type(), COMMA);
            if self.lexer.current().token != RPARENS {
                fail!("Expected RPARENS");
            }
            t
        }
    }
    else {
        self.lexer.backtrack();
        box [self.parse_type()]
    };
    let maybeContextArrow = self.lexer.next().token;
    //If there is => arrow we proceed to parse the type
    let typ = if maybeContextArrow == CONTEXTARROW {
        self.parse_type()
    }
    else if maybeContextArrow == ARROW {
	    self.lexer.backtrack();
        let mut args = box [];
        swap(&mut args, &mut maybeConstraints);
        self.parse_return_type(make_tuple_type(args))
    }
    else {//If no => was found, translate the constraint list into a type
	    self.lexer.backtrack();
        let mut args = box [];
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
			Type::new_op(self.lexer.current().value.clone(), box [])
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
	let dataName = self.require_next(NAME).value.clone();

	let mut definition = DataDefinition {
        constructors : box [],
        typ : qualified(~[], Type::new_var(intern("a"))),
        parameters : HashMap::new(),
        deriving: box []
    };
    let mut typ = TypeConstructor(TypeConstructor { name: dataName, kind: star_kind.clone() });
	while self.lexer.next().token == NAME {
        //TODO use new variables isntead of only  -1
		typ = TypeApplication(box typ, box Type::new_var(self.lexer.current().value));
		definition.parameters.insert(self.lexer.current().value.clone(), -1);
	}
    definition.typ.value = typ;
    Parser::<Iter>::set_kind(&mut definition.typ.value, 1);

	let equalToken = self.lexer.current().token;
	if equalToken != EQUALSSIGN {
		fail!(parse_error(&self.lexer, EQUALSSIGN));
	}
	definition.constructors = self.sep_by_1_func(|this| this.constructor(&definition),
		|t : &Token| t.token == PIPE);
	for ii in range(0, definition.constructors.len()) {
		definition.constructors[ii].tag = ii as int;
	}
    if self.lexer.current().token == DERIVING {
        self.require_next(LPARENS);
        definition.deriving = self.sep_by_1(|this| this.require_next(NAME).value, COMMA);
	    self.lexer.backtrack();
        self.require_next(RPARENS);
    }
    else {
	    self.lexer.backtrack();
    }
	definition
}

fn set_kind(typ: &mut Type, kind: int) {
    match typ {
        &TypeApplication(ref mut lhs, _) => {
            Parser::<Iter>::set_kind(*lhs, kind + 1)
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
				Some(Type::new_op(token.value, box []))
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
                let listType = Type::new_op_kind(intern("[]"), ~[], Kind::new(2));
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
                self.parse_return_type(Type::new_op(intern("()"), ~[]))
            }
            else {
                let t = self.parse_type();
                let maybeComma = self.lexer.next().token;
                if maybeComma == COMMA {
                    let mut tupleArgs: Vec<Type> = self.sep_by_1(|this| this.parse_type(), COMMA)
                        .move_iter()
                        .collect();
                    tupleArgs.unshift(t);
                    self.lexer.backtrack();
                    self.require_next(RPARENS);

                    self.parse_return_type(make_tuple_type(FromVec::from_vec(tupleArgs)))
                }
                else if maybeComma == RPARENS {
                    self.parse_return_type(t)
                }
                else {
                    fail!(parse_error2(&self.lexer, &[COMMA, RPARENS]))
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
				Type::new_op(token.value, FromVec::from_vec(typeArguments))
			}
			else {
                Type::new_var_args(token.value, FromVec::from_vec(typeArguments))
			};
			self.parse_return_type(thisType)
		}
	    _ => fail!("Unexpected token when parsing type {}", self.lexer.current())
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

fn sep_by_1<T>(&mut self, f : |&mut Parser<Iter>| -> T, sep : TokenEnum) -> ~[T] {
    self.sep_by_1_func(f, |tok| tok.token == sep)
}

fn sep_by_1_func<T>(&mut self, f : |&mut Parser<Iter>| -> T, sep : |&Token| -> bool) -> ~[T] {
    let mut result = Vec::new();
    loop {
        result.push(f(self));
        if !sep(self.lexer.next()) {
            break;
        }
    }
    FromVec::from_vec(result)
}
}//end impl Parser

fn make_constraints(types: ~[Type]) -> ~[Constraint] {
    FromVec::<Constraint>::from_vec(types.move_iter().map(|typ| {
        match typ {
            TypeApplication(lhs, rhs) => {
                Constraint { class: lhs.ctor().name.clone(), variables: box [rhs.var().clone()] }
            }
            _ => fail!("Parse error in constraint, non applied type")
        }
    }).collect())
}

fn make_application<I: Iterator<TypedExpr>>(f : TypedExpr, mut args : I) -> TypedExpr {
    let mut func = f;
	for a in args {
        let loc = func.location.clone();
		func = TypedExpr::with_location(Apply(box func, box a), loc);
	}
    func
}

fn make_lambda<Iter: DoubleEndedIterator<Pattern<InternedStr>>>(args : Iter, body : TypedExpr) -> TypedExpr {
	let mut body = body;
	for a in args.rev() {
        let loc = body.location.clone();
		body = TypedExpr::with_location(Lambda(a, box body), loc);
	}
    body
}

//Create a tuple with the constructor name inferred from the number of arguments passed in
fn new_tuple(arguments : ~[TypedExpr]) -> TypedExpr {
	let name = TypedExpr::new(Identifier(intern(tuple_name(arguments.len()).as_slice())));
	make_application(name, arguments.move_iter())
}

fn extract_applied_type<'a>(typ: &'a Type) -> &'a Type {
    match typ {
        &TypeApplication(ref lhs, _) => extract_applied_type(*lhs),
        _ => typ
    }
}

fn make_tuple_type(types : ~[Type]) -> Type {
    if types.len() == 1 {
        types[0]
    }
    else {
	    Type::new_op(intern(tuple_name(types.len()).as_slice()), types)
    }
}

fn parse_error2<Iter : Iterator<char>>(lexer : &Lexer<Iter>, expected : &[TokenEnum]) -> String {
    format!("Expected {} but found {}\\{{}\\}, at {}", expected, lexer.current().token, lexer.current().value.as_slice(), lexer.current().location)
    
}
fn parse_error<Iter : Iterator<char>>(lexer : &Lexer<Iter>, expected : TokenEnum) -> String {
    format!("Expected {} but found {}\\{{}\\}, at {}", expected, lexer.current().token, lexer.current().value.as_slice(), lexer.current().location)
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

fn get_contents(modulename: &str) -> IoResult<String> {
    let mut filename = String::from_str(modulename);
    filename.push_str(".hs");
    let mut file = File::open(&Path::new(filename.as_slice()));
    file.read_to_str()
}

fn parse_modules_(visited: &mut HashSet<InternedStr>, modules: &mut Vec<Module>, modulename: &str, contents: &str) -> IoResult<()> {
    let mut parser = Parser::new(contents.as_slice().chars());
    let module = parser.module();
    let interned_name = intern(modulename);
    visited.insert(interned_name);
    for import in module.imports.iter() {
        if visited.contains(&import.module) {
            fail!("Cyclic dependency in modules");
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
use parser::*;
use module::*;
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
    assert_eq!(bind.arguments, ~[IdentifierPattern(intern("x"))]);
    assert_eq!(bind.matches, Simple(op_apply(identifier("x"), intern("+"), number(3))));
    assert_eq!(bind.name, intern("test"));
}

#[test]
fn double()
{
    let mut parser = Parser::new("test = 3.14".chars());
    let bind = parser.binding();
    assert_eq!(bind.matches, Simple(rational(3.14)));
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
    let bind = Binding { arguments: ~[], name: intern("test"), typ: Default::default(),
        matches: Simple(apply(apply(identifier("add"), number(3)), number(2))) };
    assert_eq!(expr, let_(~[bind], op_apply(identifier("test"), intern("-"), number(2))));
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
            node: ConstructorPattern(intern(":"), ~[IdentifierPattern(intern("x")), IdentifierPattern(intern("xs"))])
        },
        matches: Simple(identifier("x")),
        where: None
    };
    let alt2 = Alternative {
        pattern: Located { location: Location::eof(), node: ConstructorPattern(intern("[]"), ~[]) },
        matches: Simple(number(2)),
        where: None
    };
    assert_eq!(expression, case(identifier("[]"), ~[alt, alt2]));
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

    let b = qualified(~[], bool_type());
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

    let list = Type::new_op(intern("List"), ~[Type::new_var(intern("a"))]);
    let cons = Constructor { name: intern("Cons"), tag:0, arity:2, typ: qualified(~[], function_type(&Type::new_var(intern("a")), &function_type(&list, &list))) };
    let nil = Constructor { name: intern("Nil"), tag:1, arity:0, typ: qualified(~[], list.clone()) };
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

    assert_eq!(expr, case(TypedExpr::new(TypeSig(box identifier("()"), qualified(~[], Type::new_op(intern("()"), ~[])))), 
        ~[Alternative {
        pattern: Located { location: Location::eof(), node: ConstructorPattern(intern("()"), ~[])  },
        matches: Simple(number(1)),
        where: None
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
r"class Eq a where
    (==) :: a -> a -> Bool
    (/=) x y = not (x == y)
    (/=) :: a -> a -> Bool


instance Eq a => Eq [a] where
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
r"class Eq a => Ord a where
    (<) :: a -> a -> Bool

".chars());
    let module = parser.module();

    let cls = module.classes[0];
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

    let b = TypedExpr::new(Do(~[
        DoExpr(apply(identifier("putStrLn"), identifier("test"))),
        DoBind(Located { location: Location::eof(), node: IdentifierPattern(intern("s")) }, identifier("getContents"))
        ], box apply(identifier("return"), identifier("s"))));
    assert_eq!(module.bindings[0].matches, Simple(b));
}
#[test]
fn lambda_pattern() {
    let mut parser = Parser::new(r"\(x, _) -> x".chars());
    let expr = parser.expression_();
    let pattern = ConstructorPattern(intern("(,)"), ~[IdentifierPattern(intern("x")), WildCardPattern]);
    assert_eq!(expr, TypedExpr::new(Lambda(pattern, box identifier("x"))));
}


#[test]
fn parse_imports() {
    let mut parser = Parser::new(
r"import Hello
import World

id x = x
".chars());
    let module = parser.module();

    assert_eq!(module.imports[0].module.as_slice(), "Hello");
    assert_eq!(module.imports[1].module.as_slice(), "World");
}
#[test]
fn parse_module_imports() {
    let modules = parse_modules("Test").unwrap();

    assert_eq!(modules.get(0).name.as_slice(), "Prelude");
    assert_eq!(modules.get(1).name.as_slice(), "Test");
    assert_eq!(modules.get(1).imports[0].module.as_slice(), "Prelude");
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
    let b2 = Binding { arguments: ~[IdentifierPattern(intern("x"))], name: intern("test"), typ: Default::default(),
        matches: Guards(~[
            Guard { predicate: identifier("x"), expression: number(1) },
            Guard { predicate: identifier("otherwise"), expression: number(0) },
        ])
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
    assert_eq!(module.fixity_declarations.as_slice(), &[
        FixityDeclaration { assoc: RightAssoc, precedence: 5, operators: box [intern("test")] },
        FixityDeclaration { assoc: RightAssoc, precedence: 6, operators: box [intern("test2"), intern("|<")] },
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
    let data = &module.dataDefinitions[0];
    assert_eq!(data.typ, qualified(box [], Type::new_op(intern("Test"), box [])));
    assert_eq!(data.deriving.as_slice(), &[intern("Eq"), intern("Show")]);
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
fn parse_prelude() {
    let path = &Path::new("Prelude.hs");
    let contents  = File::open(path).read_to_str().unwrap();
    let mut parser = Parser::new(contents.as_slice().chars());
    let module = parser.module();

    assert!(module.bindings.iter().any(|bind| bind.name == intern("foldl")));
    assert!(module.bindings.iter().any(|bind| bind.name == intern("id")));
    assert!(module.classes.iter().any(|class| class.name == intern("Eq")));
}

#[bench]
fn bench_prelude(b: &mut Bencher) {
    let path = &Path::new("Prelude.hs");
    let contents  = File::open(path).read_to_str().unwrap();
    b.iter(|| {
        let mut parser = Parser::new(contents.as_slice().chars());
        parser.module();
    });
}

}
