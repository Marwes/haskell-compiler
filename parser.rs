use std::mem::{swap};
use std::vec::FromVec;
use std::io::{IoResult, File};
use collections::{HashSet, HashMap};
use lexer::*;
use module::*;
use interner::*;

pub struct Parser<Iter> {
    lexer : Lexer<Iter>,
}

impl <Iter : Iterator<char>> Parser<Iter> {

pub fn new(iterator : Iter) -> Parser<Iter> {
    Parser { lexer : Lexer::new(iterator) }
}

fn requireNext<'a>(&'a mut self, expected : TokenEnum) -> &'a Token {
	let tok = self.lexer.next_().token;
	if tok != expected {
		fail!(ParseError(&self.lexer, expected));
    }
	return self.lexer.current();
}

pub fn module(&mut self) -> Module {
	let lBracketOrModule = self.lexer.module_next().token;//tokenizeModule??
	let modulename = match lBracketOrModule {
        MODULE => {
            let modulename = self.requireNext(NAME).value.clone();
            self.requireNext(WHERE);
            self.requireNext(LBRACE);
            modulename
	    }
        LBRACE => {
		    //No module declaration was found so default to Main
		    intern("Main")
	    }
        _ => fail!(ParseError(&self.lexer, LBRACE))
    };

    let mut imports = Vec::new();
    loop {
        if self.lexer.next_().token == IMPORT {
            self.lexer.backtrack();
            imports.push(self.import());
            if self.lexer.next_().token != SEMICOLON {
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
    let mut typeDeclarations = Vec::new();
    let mut dataDefinitions = Vec::new();
	loop {
		//Do a lookahead to see what the next top level binding is
		let token = self.lexer.next(toplevelError).token;
		if token == NAME || token == LPARENS {
            let mut equalOrType = self.lexer.next(bindingError).token;
            {
			    let mut numberOfLookaheads = 2;
                while equalOrType != TYPEDECL
                    && equalOrType != EQUALSSIGN
                {
                    equalOrType = self.lexer.next(bindingError).token;
                    numberOfLookaheads += 1;
                }
                for _ in range(0, numberOfLookaheads)
                {
                    self.lexer.backtrack();
                }
            }

			if equalOrType == TYPEDECL {
				let bind = self.typeDeclaration();
				typeDeclarations.push(bind);
			}
			else {
				let bind = self.binding();
                debug!("Parsed binding {}", bind.name);
				bindings.push(bind);
			}
		}
		else if token == CLASS {
			self.lexer.backtrack();
			classes.push(self.class());
		}
		else if token == INSTANCE {
			self.lexer.backtrack();
			instances.push(self.instance());
		}
		else if token == DATA {
			self.lexer.backtrack();
			dataDefinitions.push(self.dataDefinition());
		}
		else {
			break;
		}
		let semicolon = self.lexer.next(toplevelNewBindError);
        debug!("More bindings? {:?}", semicolon.token);
	    if semicolon.token != SEMICOLON {
            break;
        }
    }

	let rBracket = self.lexer.current().token;
	if rBracket != RBRACE {
		fail!(ParseError(&self.lexer, RBRACE));
	}

	let eof = self.lexer.next_();
	if eof.token != EOF {
		fail!("Unexpected token after end of module, {:?}", eof.token);
	}

	for decl in typeDeclarations.mut_iter() {
		for bind in bindings.mut_iter() {
			if decl.name == bind.name {
				bind.typeDecl = (*decl).clone();
			}
		}
	}
    Module {
        name : modulename,
        imports : FromVec::from_vec(imports),
        bindings : FromVec::from_vec(bindings),
        typeDeclarations : FromVec::from_vec(typeDeclarations),
        classes : FromVec::from_vec(classes),
        instances : FromVec::from_vec(instances),
        dataDefinitions : FromVec::from_vec(dataDefinitions)
    }
}

fn import(&mut self) -> Import {
    self.requireNext(IMPORT);
    let tok = self.requireNext(NAME);
    Import { module: tok.value }
}

fn class(&mut self) -> Class {
	self.requireNext(CLASS);

	let classname = self.requireNext(NAME).value.clone();
	let typeVariableName = self.requireNext(NAME).value.clone();
    let typeVariable = 1000000;

	self.requireNext(WHERE);
	self.requireNext(LBRACE);
	let mut typeVariableMapping = HashMap::new();
	typeVariableMapping.insert(typeVariableName, typeVariable);
	let declarations = self.sepBy1(|this| this.typeDeclaration_(&mut typeVariableMapping), SEMICOLON);
	
	self.lexer.backtrack();
	self.requireNext(RBRACE);

    //TODO infer kind from class?
	Class { name : classname, variable: TypeVariable { id: typeVariable, kind: unknown_kind.clone() }, declarations : declarations }
}

fn instance(&mut self) -> Instance {
	self.requireNext(INSTANCE);

    let mut mapping = HashMap::new();
    let (constraints, instance_type) = self.constrained_type(&mut mapping);
    match instance_type {
        TypeApplication(op, arg) => {
            let classname = match *op {
                TypeOperator(TypeOperator { name: classname, ..}) => classname,
                _ => fail!("Expected type operator")
            };
            self.requireNext(WHERE);
            self.requireNext(LBRACE);

            let mut bindings = self.sepBy1(|this| this.binding(), SEMICOLON);
            {
                let inner_type = extract_applied_type(arg);
                for bind in bindings.mut_iter() {
                    bind.name = encodeBindingIdentifier(inner_type.op().name, bind.name);
                }
            }

            self.lexer.backtrack();
            self.requireNext(RBRACE);
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
	self.parseOperatorExpression(app, 0)
}


fn parseList(&mut self) -> TypedExpr {
	let mut expressions = Vec::new();
	loop {
		match self.expression() {
            Some(expr) => expressions.push(expr),
            None => break
        }
		let comma = self.lexer.next_().token;
        if comma != COMMA {
            self.lexer.backtrack();
            break;
        }
	}
    self.requireNext(RBRACKET);

	if expressions.len() == 0 {
		return TypedExpr::new(Identifier(intern("[]")));
	}

	let mut application = {
		let mut arguments = ~[TypedExpr::new(Literal(Integral(0))), TypedExpr::new(Literal(Integral(0)))];//Must be 2 in length
		swap(&mut arguments[0], expressions.mut_last().unwrap());
		expressions.pop();
		arguments[1] = TypedExpr::new(Identifier(intern("[]")));

		makeApplication(TypedExpr::new(Identifier(intern(":"))), arguments.move_iter())
	};
	while expressions.len() > 0 {
		let mut arguments = ~[TypedExpr::new(Literal(Integral(0))), TypedExpr::new(Literal(Integral(0)))];//Must be 2 in length
		swap(&mut arguments[0], expressions.mut_last().unwrap());
		expressions.pop();
		arguments[1] = application;

		application = makeApplication(TypedExpr::new(Identifier(intern(":"))), arguments.move_iter());
	}
    application
}

fn subExpression(&mut self, parseError : |&Token| -> bool) -> Option<TypedExpr> {
	let token = self.lexer.next(parseError).token;
    debug!("Begin SubExpr {:?}", self.lexer.current());
	match token {
	    LPARENS => {
			let expressions = self.sepBy1(|this| this.expression_(), COMMA);

			let maybeParens = self.lexer.current();

			if maybeParens.token != RPARENS {
				fail!(ParseError(&self.lexer, RPARENS));
			}
			if expressions.len() == 1 {
				Some(expressions[0])
			}
			else {
				Some(newTuple(expressions))
			}
		}
	    LBRACKET => Some(self.parseList()),
	    LET => {
			let binds = self.let_bindings();

			let inToken = self.lexer.next(letExpressionEndError).token;
			if inToken != IN {
				fail!(ParseError(&self.lexer, IN));
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

			self.requireNext(OF);
			self.requireNext(LBRACE);

			let alts = self.sepBy1(|this| this.alternative(), SEMICOLON);
			let rBrace = self.lexer.current();
			if rBrace.token != RBRACE {
				fail!(ParseError(&self.lexer, RBRACE));
			}
			match expr {
                Some(e) => Some(TypedExpr::with_location(Case(box e, alts), location)),
                None => None
            }
		}
        LAMBDA => {
            let args = self.patternParameter();
            self.requireNext(ARROW);
            Some(makeLambda(args.move_iter(), self.expression_()))
        }
        DO => {
            let location = self.lexer.current().location;
            self.requireNext(LBRACE);
            let bindings = self.sepBy1(|this| this.do_binding(), SEMICOLON);
            self.lexer.backtrack();
            self.requireNext(RBRACE);
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
    if self.lexer.next_().token == LET {
        return DoLet(self.let_bindings());
    }
    debug!("Do binding {}", self.lexer.current());
    self.lexer.backtrack();
    let mut lookahead = 0;
    loop {
        lookahead += 1;
        match self.lexer.next_().token {
            SEMICOLON | RBRACE => {
                for _ in range(0, lookahead) { self.lexer.backtrack(); }
                return DoExpr(self.expression_());
            }
            LARROW => {
                for _ in range(0, lookahead) { self.lexer.backtrack(); }
                let loc = self.lexer.current().location;
                let p = Located { location: loc, node: self.pattern() };
                self.lexer.next_();//Skip <-
                return DoBind(p, self.expression_());
            }
            EOF => { fail!("Unexpected EOF") }
            _ => { debug!("Lookahead {}", self.lexer.current()); }
        }
    }
}

fn let_bindings(&mut self) -> ~[Binding] {

    self.requireNext(LBRACE);

    let binds = self.sepBy1(|this| this.binding(), SEMICOLON);

    let rBracket = self.lexer.current().token;
    if rBracket != RBRACE {
        fail!(ParseError(&self.lexer, RBRACE));
    }
    binds
}

fn alternative(&mut self) -> Alternative {
	let pat = self.located_pattern();

	self.requireNext(ARROW);

	Alternative { pattern : pat, expression : self.expression_() }
}

fn parseOperatorExpression(&mut self, inL : Option<TypedExpr>, minPrecedence : int) -> Option<TypedExpr> {
	let mut lhs = inL;
    self.lexer.next_();
    debug!("Parse operator exression, {:?}", self.lexer.current());
	while self.lexer.valid() && self.lexer.current().token == OPERATOR
		&& precedence(self.lexer.current().value.as_slice()) >= minPrecedence
	{
		let op = (*self.lexer.current()).clone();
		let mut rhs = self.application();
		self.lexer.next_();
        debug!("Parsing operator? {:?}", self.lexer.current());
		while self.lexer.valid() && self.lexer.current().token == OPERATOR
			&& precedence(self.lexer.current().value.as_slice()) >= precedence(op.value.as_slice())
		{
			let lookaheadPrecedence = precedence(self.lexer.current().value.as_slice());
			self.lexer.backtrack();
			rhs = self.parseOperatorExpression(rhs, lookaheadPrecedence);
            self.lexer.next_();
		}
		let mut name = TypedExpr::with_location(Identifier(op.value.clone()), op.location);
		let loc = match lhs {
            Some(ref l) => l.location,
            None => op.location
        };
        lhs = match (lhs, rhs) {
            (Some(lhs), Some(rhs)) => {
                let args = box [lhs, rhs];
                Some(makeApplication(name, args.move_iter()))
            }
            (Some(lhs), None) => {
                Some(TypedExpr::with_location(Apply(box name, box lhs), loc))
            }
            (None, Some(rhs)) => {
                if op.value == intern("-") {
                    match name.expr {
                        Identifier(ref mut n) => *n = intern("negate"),
                        _ => fail!("WTF")
                    }
                    let args = ~[rhs];
                    Some(makeApplication(name, args.move_iter()))
                }
                else {
                    let args = ~[TypedExpr::with_location(Identifier(intern("#")), loc), rhs];
                    let mut apply = makeApplication(name, args.move_iter());
                    apply.location = loc;
                    let params = ~[intern("#")];
                    Some(makeLambda(params.move_iter().map(|a| IdentifierPattern(a)), apply))
                }
            }
            (None, None) => return None
        };
	}
	self.lexer.backtrack();
	lhs
}

fn application(&mut self) -> Option<TypedExpr> {
    let e = self.subExpression(|_| false);
	match e {
        Some(mut lhs) => {
            let mut expressions = Vec::new();
            loop {
                let expr = self.subExpression(applicationError);
                match expr {
                    Some(e) => expressions.push(e),
                    None => break
                }
            }
            if expressions.len() > 0 {
                let loc = lhs.location;
                lhs = makeApplication(lhs, expressions.move_iter());//, loc);
                lhs.location = loc;
            }
            Some(lhs)
        }
        None => None
    }
}

fn constructor(&mut self, dataDef : &DataDefinition) -> Constructor {
	let name = self.requireNext(NAME).value.clone();
	let mut arity = 0;
    let mut mapping = dataDef.parameters.clone();
	let typ = self.constructorType(&mut arity, dataDef, &mut mapping);
	self.lexer.backtrack();
	Constructor { name : name, typ : typ, tag : 0, arity : arity }
}

fn binding(&mut self) -> Binding {
    debug!("Begin binding");
	//name1 = expr
	//or
	//name2 x y = expr
	let nameToken = self.lexer.next(errorIfNotNameOrLParens).token;
	let mut name = self.lexer.current().value.clone();
	if nameToken == LPARENS {
		//Parse a name within parentheses
		let functionName = self.lexer.next(errorIfNotNameOrOperator).token;
		if functionName != NAME && functionName != OPERATOR {
			fail!("Expected NAME or OPERATOR on left side of binding {:?}", self.lexer.current().token);
		}
		name = self.lexer.current().value.clone();

		let rParens = self.lexer.next(errorIfNotRParens).token;
		if rParens != RPARENS {
			fail!(ParseError(&self.lexer, RPARENS));
		}
	}
	else if nameToken != NAME {
		fail!(ParseError(&self.lexer, NAME));
	}

	//Parse the arguments for the binding
	let arguments = self.patternParameter();
    self.requireNext(EQUALSSIGN);

    Binding {
        name : name.clone(),
        typeDecl : TypeDeclaration {
            context : box [],
            typ : Type::new_var(-1),
            name : name
        },
        arity : arguments.len(),
        arguments: arguments,
        expression : self.expression_(),
    }
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

fn patternParameter(&mut self) -> ~[Pattern] {
	let mut parameters = Vec::new();
	loop {
		let token = self.lexer.next_().token;
		match token {
            NAME => {
                let name = self.lexer.current().value;
                let p = self.make_pattern(name, |_| ~[]);
                parameters.push(p);
            }
            NUMBER => parameters.push(NumberPattern(from_str(self.lexer.current().value.as_slice()).unwrap())),
		    LPARENS => {
				let pat = self.pattern();
				let maybeComma = self.lexer.next_().token;
				if maybeComma == COMMA {
					let mut tupleArgs: Vec<Pattern> = self.sepBy1(|this| this.pattern(), COMMA).move_iter().collect();

					let rParens = self.lexer.current();
					if rParens.token != RPARENS {
						fail!(ParseError(&self.lexer, RPARENS));
					}
					tupleArgs.unshift(pat);
					parameters.push(ConstructorPattern(tuple_name(tupleArgs.len()), FromVec::from_vec(tupleArgs)));
				}
				else {
                    self.lexer.backtrack();
                    self.requireNext(RPARENS);
                    parameters.push(pat);
				}
			}
            LBRACKET => {
                if self.lexer.next_().token != RBRACKET {
                    fail!(ParseError(&self.lexer, RBRACKET));
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
    let location = self.lexer.next_().location;
    self.lexer.backtrack();
    Located { location: location, node: self.pattern() }
}

fn pattern(&mut self) -> Pattern {
	let nameToken = self.lexer.next_().token;
    let name = self.lexer.current().value.clone();
    let pat = match nameToken {
        LBRACKET => {
            if self.lexer.next_().token != RBRACKET {
                fail!(ParseError(&self.lexer, RBRACKET));
            }
            ConstructorPattern(intern("[]"), ~[])
        }
        NAME | OPERATOR => self.make_pattern(name, |this| this.patternParameter()),
        NUMBER => NumberPattern(from_str(name.as_slice()).unwrap()),
        LPARENS => {
            let tupleArgs = self.sepBy1(|this| this.pattern(), COMMA);
            let rParens = self.lexer.current().token;
            if rParens != RPARENS {
                fail!(ParseError(&self.lexer, RPARENS));
            }
            ConstructorPattern(tuple_name(tupleArgs.len()), tupleArgs)
        }
        _ => { fail!("Error parsing pattern at token {}", self.lexer.current()) }
    };
    self.lexer.next_();
    if self.lexer.current().token == OPERATOR && self.lexer.current().value.as_slice() == ":" {
        ConstructorPattern(self.lexer.current().value, ~[pat, self.pattern()])
    }
    else {
        self.lexer.backtrack();
        pat
    }
}

fn typeDeclaration(&mut self) -> TypeDeclaration {
	let mut typeVariableMapping = HashMap::new();
	self.typeDeclaration_(&mut typeVariableMapping)
}

fn typeDeclaration_(&mut self, typeVariableMapping : &mut HashMap<InternedStr, int>) -> TypeDeclaration {
    let mut name;
	{
        let nameToken = self.lexer.next(errorIfNotNameOrLParens).token;
        name = self.lexer.current().value.clone();
        if nameToken == LPARENS {
            //Parse a name within parentheses
            let functionName = self.lexer.next(errorIfNotNameOrOperator).token;
            if functionName != NAME && functionName != OPERATOR {
                fail!("Expected NAME or OPERATOR on left side of binding {:?}", functionName);
            }
            name = self.lexer.current().value.clone();
            let rParens = self.lexer.next(errorIfNotRParens).token;
            if rParens != RPARENS {
                fail!(ParseError(&self.lexer, RPARENS));
            }
        }
        else if nameToken != NAME {
            fail!(ParseError(&self.lexer, NAME));
        }
    }
	let decl = self.lexer.next_().token;
	if decl != TYPEDECL {
		fail!(ParseError(&self.lexer, TYPEDECL));
	}
    let (context, typ) = self.constrained_type(typeVariableMapping);
	TypeDeclaration { name : name, typ : typ, context : context }
}

fn constrained_type(&mut self, typeVariableMapping : &mut HashMap<InternedStr, int>) -> (~[Constraint], Type) {
    let mut variableIndex = 0;
    let mut maybeConstraints = if self.lexer.next_().token == LPARENS {
        let t = self.sepBy1(|this| this.parse_type_(&mut variableIndex, typeVariableMapping), COMMA);
        if self.lexer.current().token != RPARENS {
            fail!("Expected RPARENS");
        }
        t
    }
    else {
        self.lexer.backtrack();
        box [self.parse_type_(&mut variableIndex, typeVariableMapping)]
    };
    let maybeContextArrow = self.lexer.next_().token;
    //If there is => arrow we proceed to parse the type
    let typ = if maybeContextArrow == CONTEXTARROW {
        self.parse_type_(&mut variableIndex, typeVariableMapping)
    }
    else if maybeContextArrow == ARROW {
	    self.lexer.backtrack();
        let mut args = box [];
        swap(&mut args, &mut maybeConstraints);
        self.parse_return_type(tupleType(args), &mut variableIndex, typeVariableMapping)
    }
    else {//If no => was found, translate the constraint list into a type
	    self.lexer.backtrack();
        let mut args = box [];
        swap(&mut args, &mut maybeConstraints);
        tupleType(args)
    };
	(make_constraints(maybeConstraints), typ)
}

fn constructorType(&mut self, arity : &mut int, dataDef: &DataDefinition, mapping : &mut HashMap<InternedStr, int>) -> Type
{
	let token = self.lexer.next(constructorError).token;
	if token == NAME {
		*arity += 1;
		let arg = if self.lexer.current().value.as_slice().char_at(0).is_lowercase() {
			match mapping.find(&self.lexer.current().value) {
                Some(existingVariable) => Type::new_var(*existingVariable),
                None => fail!("Undefined type parameter {:?}", self.lexer.current().value)
            }
		}
		else {
			Type::new_op(self.lexer.current().value.clone(), box [])
        };
        function_type(&arg, &self.constructorType(arity, dataDef, mapping))
	}
	else if token == LPARENS {
        *arity += 1;
        let mut var = 100000;
        let arg = self.parse_type_(&mut var, mapping);
        self.requireNext(RPARENS);
        function_type(&arg, &self.constructorType(arity, dataDef, mapping))
    }
    else {
		dataDef.typ.clone()
	}
}


fn dataDefinition(&mut self) -> DataDefinition {
	self.requireNext(DATA);
	let dataName = self.requireNext(NAME).value.clone();

	let mut definition = DataDefinition {
        constructors : box [],
        typ : Type::new_var(0),
        parameters : HashMap::new()
    };
    let mut typ = TypeOperator(TypeOperator { name: dataName, kind: star_kind.clone() });
	while self.lexer.next_().token == NAME {
        //TODO use new variables isntead of only  -1
		typ = TypeApplication(box typ, box Type::new_var(-1));
		definition.parameters.insert(self.lexer.current().value.clone(), -1);
	}
    definition.typ = typ;
    Parser::<Iter>::set_kind(&mut definition.typ, 1);

	let equalToken = self.lexer.current().token;
	if equalToken != EQUALSSIGN {
		fail!(ParseError(&self.lexer, EQUALSSIGN));
	}
	definition.constructors = self.sepBy1_func(|this| this.constructor(&definition),
		|t : &Token| t.token == PIPE);
	for ii in range(0, definition.constructors.len()) {
		definition.constructors[ii].tag = ii as int;
	}
	self.lexer.backtrack();
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

fn sub_type(&mut self, variableIndex: &mut int, typeVariableMapping: &mut HashMap<InternedStr, int>) -> Option<Type> {
	let token = (*self.lexer.next_()).clone();
	match token.token {
	    LBRACKET => {
            self.lexer.backtrack();
            Some(self.parse_type_(variableIndex, typeVariableMapping))
		}
	    LPARENS => {
            self.lexer.backtrack();
			Some(self.parse_type_(variableIndex, typeVariableMapping))
		}
	    NAME => {
			if token.value.as_slice().char_at(0).is_uppercase() {
				Some(Type::new_op(token.value, box []))
			}
			else {
                let t = typeVariableMapping.find_or_insert(token.value, *variableIndex);
                *variableIndex += 1;
				Some(Type::new_var(*t))
			}
		}
        _ => { self.lexer.backtrack(); None }
	}
}

fn parse_type_(&mut self, variableIndex: &mut int, typeVariableMapping : &mut HashMap<InternedStr, int>) -> Type {
	let token = (*self.lexer.next_()).clone();
	match token.token {
	    LBRACKET => {
            if self.lexer.next_().token == RBRACKET {
                let listType = Type::new_op_kind(intern("[]"), ~[], Kind::new(2));
                self.parse_return_type(listType, variableIndex, typeVariableMapping)
            }
            else {
                self.lexer.backtrack();
                let t = self.parse_type_(variableIndex, typeVariableMapping);
                self.requireNext(RBRACKET);
                let listType = list_type(t);
                
                self.parse_return_type(listType, variableIndex, typeVariableMapping)
            }
		}
	    LPARENS => {
			let t = self.parse_type_(variableIndex, typeVariableMapping);
			let maybeComma = self.lexer.next_().token;
			if maybeComma == COMMA {
				let mut tupleArgs: Vec<Type> = self.sepBy1(|this| this.parse_type_(variableIndex, typeVariableMapping), COMMA)
                    .move_iter()
                    .collect();
				tupleArgs.unshift(t);
                self.lexer.backtrack();
                self.requireNext(RPARENS);

                self.parse_return_type(tupleType(FromVec::from_vec(tupleArgs)), variableIndex, typeVariableMapping)
			}
			else if maybeComma == RPARENS {
                self.parse_return_type(t, variableIndex, typeVariableMapping)
			}
            else {
                fail!(ParseError2(&self.lexer, &[COMMA, RPARENS]))
            }
		}
	    NAME => {
			let mut typeArguments = Vec::new();
            loop {
                match self.sub_type(variableIndex, typeVariableMapping) {
                    Some(typ) => typeArguments.push(typ),
                    None => break
                }
            }

			let thisType = if token.value.as_slice().char_at(0).is_uppercase() {
				Type::new_op(token.value, FromVec::from_vec(typeArguments))
			}
			else {
                let t = typeVariableMapping.find_or_insert(token.value, *variableIndex);
                *variableIndex += 1;
                Type::new_var_args(*t, FromVec::from_vec(typeArguments))
			};
			self.parse_return_type(thisType, variableIndex, typeVariableMapping)
		}
	    _ => fail!("Unexpected token when parsing type {:?}", self.lexer.current())
	}
}

fn parse_return_type(&mut self, typ : Type, variableIndex: &mut int, typeVariableMapping : &mut HashMap<InternedStr, int>) -> Type {

    let arrow = self.lexer.next_().token;
    if arrow == ARROW {
        return function_type(&typ, &self.parse_type_(variableIndex, typeVariableMapping));
    }
    else {
        self.lexer.backtrack();
        return typ
    }
}

fn sepBy1<T>(&mut self, f : |&mut Parser<Iter>| -> T, sep : TokenEnum) -> ~[T] {
    self.sepBy1_func(f, |tok| tok.token == sep)
}

fn sepBy1_func<T>(&mut self, f : |&mut Parser<Iter>| -> T, sep : |&Token| -> bool) -> ~[T] {
    let mut result = Vec::new();
    loop {
        result.push(f(self));
        if !sep(self.lexer.next_()) {
            break;
        }
    }
    FromVec::from_vec(result)
}
}//end impl Parser

fn precedence(s : &str) -> int {
    match s {
        "+" => 1,
        "-" => 1,
        "==" => 1,
        "/=" => 1,
        "<" => 1,
        ">" => 1,
        "<=" => 1,
        ">=" => 1,
        "*" => 3,
        "/" => 3,
        "%" => 3,
        _ => 9
    }
}
fn make_constraints(types: ~[Type]) -> ~[Constraint] {
    FromVec::<Constraint>::from_vec(types.move_iter().map(|typ| {
        match typ {
            TypeApplication(lhs, rhs) => {
                Constraint { class: lhs.op().name.clone(), variables: box [rhs.var().clone()] }
            }
            _ => fail!("Parse error in constraint, non applied type")
        }
    }).collect())
}



fn toplevelError(t : &Token) -> bool {
	return t.token != NAME
		&& t.token != RBRACKET
		&& t.token != SEMICOLON
		&& t.token != DATA
		&& t.token != LPARENS
		&& t.token != CLASS
		&& t.token != INSTANCE;
}

fn toplevelNewBindError(t : &Token) -> bool {
	return t.token != RBRACKET
		&& t.token != SEMICOLON;
}

fn bindingError(t : &Token) -> bool {
	return t.token != EQUALSSIGN
		&& t.token != NAME
		&& t.token != TYPEDECL
		&& t.token != OPERATOR
        && t.token != LPARENS
		&& t.token != RPARENS
        && t.token != LBRACKET
        && t.token != RBRACKET;
}

fn constructorError(tok : &Token) -> bool {
	return tok.token != NAME
		&& tok.token != OPERATOR
		&& tok.token != LPARENS
        && tok.token != PIPE;
}

fn tuple_name(size : uint) -> InternedStr {
	let mut name = StrBuf::with_capacity(size+1);
    name.push_char('(');
    for _ in range(1, size) {
        name.push_char(',');
    }
	name.push_char(')');
	intern(name.as_slice())
}

fn makeApplication<I: Iterator<TypedExpr>>(f : TypedExpr, mut args : I) -> TypedExpr {
    let mut func = f;
	for a in args {
        let loc = func.location.clone();
		func = TypedExpr::with_location(Apply(box func, box a), loc);
	}
    func
}

fn makeLambda<Iter: DoubleEndedIterator<Pattern<InternedStr>>>(args : Iter, body : TypedExpr) -> TypedExpr {
	let mut body = body;
	for a in args.rev() {
        let loc = body.location.clone();
		body = TypedExpr::with_location(Lambda(a, box body), loc);
	}
    body
}

//Create a tuple with the constructor name inferred from the number of arguments passed in
fn newTuple(arguments : ~[TypedExpr]) -> TypedExpr {
	let name = TypedExpr::new(Identifier(tuple_name(arguments.len())));
	makeApplication(name, arguments.move_iter())
}

fn letExpressionEndError(t : &Token) -> bool {
	t.token != IN
}

fn applicationError(t :&Token) -> bool {
	return t.token != LPARENS
		&& t.token != RPARENS
		&& t.token != LBRACKET
		&& t.token != RBRACKET
		&& t.token != LET
		&& t.token != OF
		&& t.token != NAME
		&& t.token != NUMBER
		&& t.token != FLOAT
		&& t.token != OPERATOR
		&& t.token != SEMICOLON
		&& t.token != COMMA
        && t.token != CHAR
        && t.token != STRING;
}


fn errorIfNotNameOrLParens(tok : &Token) -> bool {
    tok.token != NAME && tok.token != LPARENS
}
fn errorIfNotNameOrOperator(tok : &Token) -> bool {
	tok.token != NAME && tok.token != OPERATOR
}

fn errorIfNotRParens(tok : &Token) -> bool {
	tok.token != RPARENS
}

fn extract_applied_type<'a>(typ: &'a Type) -> &'a Type {
    match typ {
        &TypeApplication(ref lhs, _) => extract_applied_type(*lhs),
        _ => typ
    }
}

fn tupleType(types : ~[Type]) -> Type {
    if types.len() == 1 {
        types[0]
    }
    else {
	    Type::new_op(tuple_name(types.len()), types)
    }
}

fn ParseError2<Iter : Iterator<char>>(lexer : &Lexer<Iter>, expected : &[TokenEnum]) -> StrBuf {
    format!("Expected {:?} but found {:?}\\{{}\\}, at {}", expected, lexer.current().token, lexer.current().value.as_slice(), lexer.current().location)
    
}
fn ParseError<Iter : Iterator<char>>(lexer : &Lexer<Iter>, expected : TokenEnum) -> StrBuf {
    format!("Expected {:?} but found {:?}\\{{}\\}, at {}", expected, lexer.current().token, lexer.current().value.as_slice(), lexer.current().location)
}
fn encodeBindingIdentifier(instancename : InternedStr, bindingname : InternedStr) -> InternedStr {
    let mut buffer = StrBuf::new();
    buffer.push_str("#");
    buffer.push_str(instancename.clone().as_slice());
    buffer.push_str(bindingname.clone().as_slice());
    intern(buffer.as_slice())
}

pub fn parse_modules(modulename: &str) -> IoResult<Vec<Module>> {
    let mut modules = Vec::new();
    let mut visited = HashSet::new();
    try!(parse_modules_(&mut visited, &mut modules, modulename));
    Ok(modules)
}
pub fn parse_modules_(visited: &mut HashSet<InternedStr>, modules: &mut Vec<Module>, modulename: &str) -> IoResult<()> {
    let contents = {
        let mut filename = StrBuf::from_str(modulename);
        filename.push_str(".hs");
        let mut file = File::open(&Path::new(filename.as_slice()));
        try!(file.read_to_str())
    };
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
            try!(parse_modules_(visited, modules, import.module.as_slice()));
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
use typecheck::{function_type, identifier, apply, number, rational, lambda, let_, case};
use std::io::File;
use test::Bencher;


#[test]
fn simple()
{
    let mut parser = Parser::new("2 + 3".chars());
    let expr = parser.expression_();
    assert_eq!(expr, apply(apply(identifier("+"), number(2)), number(3)));
}
#[test]
fn binding()
{
    let mut parser = Parser::new("test x = x + 3".chars());
    let bind = parser.binding();
    assert_eq!(bind.arguments, ~[IdentifierPattern(intern("x"))]);
    assert_eq!(bind.expression, apply(apply(identifier("+"), identifier("x")), number(3)));
    assert_eq!(bind.name, intern("test"));
}

#[test]
fn double()
{
    let mut parser = Parser::new("test = 3.14".chars());
    let bind = parser.binding();
    assert_eq!(bind.expression, rational(3.14));
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
    let mut bind = Binding { arity: 0, arguments: ~[], name: intern("test"), typeDecl:Default::default(),
        expression: apply(apply(identifier("add"), number(3)), number(2)) };
    bind.typeDecl.name = intern("test");
    assert_eq!(expr, let_(~[bind], apply(apply(identifier("-"), identifier("test")), number(2))));
}

#[test]
fn parse_case() {
    let mut parser = Parser::new(
r"case [] of
    : x xs -> x
    [] -> 2
".chars());
    let expression = parser.expression_();
    let alt = Alternative {
        pattern: Located {
            location: Location::eof(),
            node: ConstructorPattern(intern(":"), ~[IdentifierPattern(intern("x")), IdentifierPattern(intern("xs"))])
        },
        expression: identifier("x") };
    let alt2 = Alternative {
        pattern: Located { location: Location::eof(), node: ConstructorPattern(intern("[]"), ~[]) },
        expression: number(2) };
    assert_eq!(expression, case(identifier("[]"), ~[alt, alt2]));
}

#[test]
fn parse_type() {
    let mut parser = Parser::new(
r"(.) :: (b -> c) -> (a -> b) -> (a -> c)".chars());
    let typeDecl = parser.typeDeclaration();
    let a = &Type::new_var(0);
    let b = &Type::new_var(1);
    let c = &Type::new_var(2);
    let f = function_type(&function_type(b, c), &function_type(&function_type(a, b), &function_type(a, c)));

    assert_eq!(typeDecl.name, intern("."));
    assert_eq!(typeDecl.typ, f);
}
#[test]
fn parse_data() {
    let mut parser = Parser::new(
r"data Bool = True | False".chars());
    let data = parser.dataDefinition();

    let b = bool_type();
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
    let data = parser.dataDefinition();

    let list = Type::new_op(intern("List"), ~[Type::new_var(0)]);
    let cons = Constructor { name: intern("Cons"), tag:0, arity:2, typ: function_type(&Type::new_var(0), &function_type(&list, &list))};
    let nil = Constructor { name: intern("Nil"), tag:1, arity:0, typ: list.clone() };
    assert_eq!(data.typ, list);
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
fn test_operators() {
    let mut parser = Parser::new("1 : 2 : []".chars());
    let expr = parser.expression_();
    assert_eq!(expr, apply(apply(identifier(":"), number(1)), apply(apply(identifier(":"), number(2)), identifier("[]"))));
}

#[test]
fn parse_instance_class() {
    let mut parser = Parser::new(
r"class Eq a where
    (==) :: a -> a -> Bool

instance Eq a => Eq [a] where
    (==) xs ys = undefined".chars());
    let module = parser.module();

    assert_eq!(module.classes[0].name, intern("Eq"));
    assert_eq!(module.instances[0].classname, intern("Eq"));
    assert_eq!(module.instances[0].constraints[0].class, intern("Eq"));
    assert_eq!(module.instances[0].typ, list_type(Type::new_var(0)));
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
    assert_eq!(module.bindings[0].expression, b);
}
#[test]
fn lambda_pattern() {
    let mut parser = Parser::new(r"(\(x, _) -> x)".chars());
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
