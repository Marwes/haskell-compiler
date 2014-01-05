use std::str::{from_chars};
use std::util::{swap};
use std::hashmap::HashMap;
use lexer::*;
use lexer::{Lexer, Token, TokenEnum,
    EOF, NAME, OPERATOR, NUMBER, FLOAT, LPARENS, RPARENS, LBRACKET, RBRACKET, LBRACE, RBRACE, INDENTSTART, INDENTLEVEL, COMMA, EQUALSSIGN, SEMICOLON, MODULE, CLASS, INSTANCE, WHERE, LET, IN, CASE, OF, ARROW, TYPEDECL, DATA
};
use typecheck::{Type, TypeVariable, TypeOperator, Expr, Identifier, Number, Apply, Lambda, Let, TypedExpr, function_type};

mod lexer;

struct Module {
    name : ~str,
    bindings : ~[Binding],
    typeDeclarations : ~[TypeDeclaration],
    classes : ~[Class],
    instances : ~[Instance],
    dataDefinitions : ~[DataDefinition]
}

struct Class {
    name : ~str,
    declarations : ~[TypeDeclaration]
}

struct Instance {
    bindings : ~[Binding],
    typ : TypeOperator,
    classname : ~str
}

struct Binding {
    name : ~str,
    expression : TypedExpr,
    typeDecl : TypeDeclaration
}

struct Constructor {
    name : ~str,
    typ : Type,
    tag : int,
    arity : int
}

struct DataDefinition {
    constructors : ~[Constructor],
    typ : TypeOperator,
    parameters : HashMap<~str, Type>
}

struct TypeDeclaration {
    context : ~[TypeOperator],
    typ : Type,
    name : ~str
}

struct Alternative {
    pattern : Pattern,
    expression : TypedExpr
}

enum Pattern {
    NumberPattern(int),
    IdentifierPattern(~str),
    ConstructorPattern(~str, ~[Pattern])
}

struct Parser<Iter> {
    lexer : Lexer<Iter>,
}

impl <Iter : Iterator<char>> Parser<Iter> {

fn requireNext<'a>(&'a mut self, expected : TokenEnum) -> &'a Token {
	let tok = self.lexer.next_();
	if (tok.token != expected) {
		fail!(ParseError(&self.lexer, expected));
    }
	return tok;
}

fn module(&mut self) -> Module {
	let lBracketOrModule = self.lexer.next_();//tokenizeModule??
	let modulename = match lBracketOrModule.token {
        MODULE => {
            let modulename = self.requireNext(NAME);
            self.requireNext(WHERE);
            self.requireNext(LBRACE);
            modulename.value
	    }
        LBRACE => {
		    //No module declaration was found so default to Main
		    ~"Main"
	    }
        _ => fail!(ParseError(&self.lexer, LBRACE))
    };

    let mut classes = ~[];
    let mut bindings = ~[];
    let mut instances = ~[];
    let mut typeDeclarations = ~[];
    let mut dataDefinitions = ~[];
	loop {
		//Do a lookahead to see what the next top level binding is
		let token = self.lexer.next(toplevelError);
		if (token.token == NAME || token.token == LPARENS)
		{
			let numberOfLookaheads = 2;
			let mut equalOrType = &self.lexer.next(bindingError);
			while (equalOrType.token != TYPEDECL
				&& equalOrType.token != EQUALSSIGN)
			{
				equalOrType = &self.lexer.next(bindingError);
				numberOfLookaheads += 1;
			}
			for _ in range(0, numberOfLookaheads)
			{
				self.lexer.backtrack();
			}

			if (equalOrType.token == TYPEDECL)
			{
				let bind = self.typeDeclaration();
				typeDeclarations.push(bind);
			}
			else
			{
				let bind = self.binding();
				bindings.push(bind);
			}
		}
		else if (token.token == CLASS)
		{
			self.lexer.backtrack();
			classes.push(self.class());
		}
		else if (token.token == INSTANCE)
		{
			self.lexer.backtrack();
			instances.push(self.instance());
		}
		else if (token.token == DATA)
		{
			self.lexer.backtrack();
			dataDefinitions.push(self.dataDefinition());
		}
		else
		{
			break;
		}
		let semicolon = self.lexer.next(toplevelNewBindError);
	    if (semicolon.token != SEMICOLON) {
            break;
        }
    }

	let rBracket = self.lexer.current();
	if (rBracket.token != RBRACE)
	{
		fail!(ParseError(&self.lexer, RBRACE));
	}

	let eof = self.lexer.next_();
	if (eof.token != EOF)
	{
		fail!("Unexpected token after end of module, {:?}", eof.token);
	}

	for decl in typeDeclarations.iter()
	{
		for bind in bindings.iter()
		{
			if (decl.name == bind.name)
			{
				bind.typeDecl = *decl.clone();
			}
		}
	}
    Module {
        name : modulename,
        bindings : bindings,
        typeDeclarations : typeDeclarations,
        classes : classes,
        instances : instances,
        dataDefinitions : dataDefinitions }
}

fn class(&mut self) -> Class {
	self.requireNext(CLASS);

	let classname = self.requireNext(NAME).value;
	let typeVariableName = self.requireNext(NAME).value;
    let typeVariable = TypeVariable { id : 100 };

	self.requireNext(WHERE);
	self.requireNext(LBRACE);
	let typeVariableMapping = HashMap::new();
	typeVariableMapping.insert(typeVariableName, typeVariable);
	let declarations = self.sepBy1(|this| this.typeDeclaration_(&typeVariableMapping), SEMICOLON);
	
	self.lexer.backtrack();
	self.requireNext(RBRACE);

	Class { name : classname, declarations : declarations }
}

fn instance(&mut self) -> Instance {
	self.requireNext(INSTANCE);

	let classname = self.requireNext(NAME).value;
	
	let typ = match self.parse_type() {
        TypeOperator(op) => op,
        _ => fail!("Expected type operator")
    };

	self.requireNext(WHERE);
	self.requireNext(LBRACE);

	let mut bindings = self.sepBy1(|this| this.binding(), SEMICOLON);
	for bind in bindings.iter()
	{
		bind.name = encodeBindingIdentifier(typ.name, bind.name);
	}

	self.lexer.backtrack();
	self.requireNext(RBRACE);
	Instance { typ : typ, classname : classname, bindings : bindings }
}

fn expression_(&mut self) -> TypedExpr {
    match self.expression() {
        Some(expr) => expr,
        None => fail!("Failed to parse expression at {:?}", "ASD")
    }
}

fn expression(&mut self) -> Option<TypedExpr> {
	let app = self.application();
	self.parseOperatorExpression(app, 0)
}


fn parseList(&mut self) -> TypedExpr {
	let expressions = ~[];
	let mut comma;
	loop {
		match self.expression() {
            Some(expr) => expressions.push(expr),
            None => break
        }
		comma = &self.lexer.next_();
        if (comma.token != COMMA) {
            break;
        }
	}

	if (expressions.len() == 0)
	{
		return TypedExpr::new(Identifier(~"[]"));
	}

	let application;
	{
		let arguments = ~[TypedExpr::new(Number(0)), TypedExpr::new(Number(0))];//Must be 2 in length
		swap(&arguments[0], &expressions[expressions.len() - 1]);
		expressions.pop();
		arguments[1] = TypedExpr::new(Identifier(~"[]"));

		application = makeApplication(TypedExpr::new(Identifier(~":")), arguments);
	}
	while (expressions.len() > 0)
	{
		let arguments = ~[TypedExpr::new(Number(0)), TypedExpr::new(Number(0))];//Must be 2 in length
		swap(&arguments[0], &expressions[expressions.len() - 1]);
		expressions.pop();
		arguments[1] = application;

		application = makeApplication(TypedExpr::new(Identifier(~":")), arguments);
	}

	let maybeParens = self.lexer.current();
	if (maybeParens.token != RBRACKET)
	{
		fail!(ParseError(&self.lexer, RBRACKET));
	}
	else
	{
		return application;
	}
}

fn subExpression(&mut self, parseError : |&Token| -> bool) -> Option<TypedExpr> {
	let token = self.lexer.next(parseError);
	match token.token {
	    LPARENS =>
		{
			let expressions = self.sepBy1(|this| this.expression_(), COMMA);

			let maybeParens = self.lexer.current();

			if (maybeParens.token != RPARENS)
			{
				fail!(ParseError(&self.lexer, RPARENS));
			}
			if (expressions.len() == 1)
			{
				Some(expressions[0])
			}
			else
			{
				Some(newTuple(expressions))
			}
		}
	    LBRACKET => Some(self.parseList()),
	    LET =>
		{
			self.requireNext(LBRACE);

			let binds = self.sepBy1(|this| this.binding(), SEMICOLON);

			let rBracket = self.lexer.current();
			if (rBracket.token != RBRACE)
			{
				fail!(ParseError(&self.lexer, RBRACE));
			}
			let inToken = self.lexer.next(letExpressionEndError);
			if (inToken.token != IN) {
				fail!(ParseError(&self.lexer, IN));
            }
			match self.expression() {
                Some(e) => {
                    let x = ~[];
                    for bind in binds.iter() {
                        x.push((bind.name, ~bind.expression));
                    }
                    Some(TypedExpr::new(Let(x, ~e)))
                }
                None => None
            }
		}
        /*
	    CASE =>
		{
			let expr = self.expression();

			self.requireNext(OF);
			self.requireNext(LBRACE);

			let alts = self.sepBy1(&Parser::alternative, SEMICOLON);
			let rBrace = self.lexer.current();
			if (rBrace.token != RBRACE)
			{
				fail!(ParseError(&self.lexer, RBRACE));
			}
			return TypedExpr::with_location(Case(expr, alts), token.location);
		}*/
        NAME => Some(TypedExpr::with_location(Identifier(token.value), token.location)),
        NUMBER => Some(TypedExpr::with_location(Number(from_str(token.value).unwrap()), token.location)),
	    //FLOAT => TypedExpr::with_location(Rational(token.value.from_str()), token.location),
	    _ => {
		self.lexer.backtrack();
        None
        }
    }
}

fn alternative(&mut self) -> Alternative {
	let pat = self.pattern();

	self.requireNext(ARROW);

	Alternative { pattern : pat, expression : self.expression_() }
}

fn parseOperatorExpression(&mut self, lhs : Option<TypedExpr>, minPrecedence : int) -> Option<TypedExpr> {
	self.lexer.next_();
	let f = self.lexer.current();
	while (self.lexer.valid() && self.lexer.current().token == OPERATOR
		&& precedence(self.lexer.current().value) >= minPrecedence)
	{
		let op = self.lexer.current();
		let rhs = self.application();
		let nextOP = self.lexer.next_();
		while (self.lexer.valid() && nextOP.token == OPERATOR
			&& precedence(nextOP.value) > precedence(op.value))
		{
			let lookahead = self.lexer.current();
			self.lexer.backtrack();
			rhs = self.parseOperatorExpression(rhs, precedence(lookahead.value));
			self.lexer.next_();
		}
		let name = TypedExpr::with_location(Identifier(op.value), op.location);
		let loc = match lhs {
            Some(l) => l.location,
            None => op.location
        };
        match (lhs, rhs) {
            (Some(lhs), Some(rhs)) => {
                let args = ~[lhs, rhs];
                lhs = makeApplication(name, args);
                lhs.location = loc;
            }
            (Some(lhs), None) => {
                let args = ~[lhs, TypedExpr::with_location(Identifier(~"#"), loc)];
                let mut apply = makeApplication(name, args);
                apply.location = loc;
                let params = ~[~"#"];
                lhs = makeLambda(params, apply);
                lhs.location  =loc;
            }
            (None, Some(rhs)) => {
                if (op.value == ~"-")
                {
                    match name.expr {
                        Identifier(ref mut n) => *n = ~"negate",
                        _ => fail!("WTF")
                    }
                    let args = ~[rhs];
                    let l = makeApplication(name, args);
                    l.location = loc;
                    lhs = Some(l);
                }
                else
                {
                    let args = ~[TypedExpr::with_location(Identifier(~"#"), loc), rhs];
                    let mut apply = makeApplication(name, args);
                    apply.location = loc;
                    let params = ~[~"#"];
                    let l = makeLambda(params, apply);
                    l.location = loc;
                    lhs = Some(l);
                }
            }
            (None, None) => return None
        }
	}
	self.lexer.backtrack();
	lhs
}

fn application(&mut self) -> Option<TypedExpr> {
    let e = self.subExpression(|t| false);
	match e {
        Some(lhs) => {
            let mut expressions = ~[];
            loop {
                let expr = self.subExpression(applicationError);
                match expr {
                    Some(e) => expressions.push(e),
                    None => break
                }
            }
            if (expressions.len() > 0)
            {
                let loc = lhs.location;
                lhs = makeApplication(lhs, expressions);//, loc);
            }
            Some(lhs)
        }
        None => None
    }
}

fn constructor(&mut self, dataDef : &DataDefinition) -> Constructor {
	let nameToken = self.lexer.next_();
	let mut arity = 0;
	let typ = self.constructorType(&mut arity, dataDef);
	self.lexer.backtrack();
	Constructor { name : nameToken.value, typ : typ, tag : 0, arity : arity }
}

fn binding(&mut self) -> Binding {
	//name1 = expr
	//or
	//name2 x y = expr
	let nameToken = self.lexer.next(errorIfNotNameOrLParens);
	let name = nameToken.value;
	if (nameToken.token == LPARENS)
	{
		//Parse a name within parentheses
		let functionName = self.lexer.next(errorIfNotNameOrOperator);
		if (functionName.token != NAME && functionName.token != OPERATOR)
		{
			fail!("Expected NAME or OPERATOR on left side of binding {:?}", functionName.token);
		}
		name = functionName.value;
		let rParens = self.lexer.next(errorIfNotRParens);
		if (rParens.token != RPARENS)
		{
			fail!(ParseError(&self.lexer, RPARENS));
		}
	}
	else if (nameToken.token != NAME)
	{
		fail!(ParseError(&self.lexer, NAME));
	}

	//Parse the arguments for the binding
	let mut arguments = ~[];
	while (true)
	{
		let token = self.lexer.next(errorIfNotNameOrEqual);
		if (token.token == NAME)
		{
			arguments.push(token.value);
		}
		else
		{
			break;
		}
	}
	if (self.lexer.current().token != EQUALSSIGN)
	{
		fail!(ParseError(&self.lexer, EQUALSSIGN));
	}
	if (arguments.len() > 0)
    {
		let lambda = makeLambda(arguments, self.expression_());
		Binding { name : name, typeDecl : TypeDeclaration { context : ~[], typ : Type::new_var(-1), name : ~"" }, expression : lambda }
	}
	else
	{
		Binding { name : name, typeDecl : TypeDeclaration { context : ~[], typ : Type::new_var(-1), name : ~"" }, expression : self.expression_() }
	}
}


fn patternParameter(&mut self) -> ~[Pattern] {
	let mut parameters = ~[];
	loop {
		let token = self.lexer.next_();
		match token.token
		{
            NAME => parameters.push(IdentifierPattern(token.value)),
            NUMBER => parameters.push(NumberPattern(from_str(token.value).unwrap())),
		    LPARENS =>
			{
				let pat = self.pattern();
				let maybeComma = self.lexer.next_();
				if (maybeComma.token == COMMA)
				{
					let tupleArgs = self.sepBy1(|this| this.pattern(), COMMA);
					let rParens = self.lexer.current();
					if (rParens.token != RPARENS)
					{
						fail!(ParseError(&self.lexer, RPARENS));
					}
					tupleArgs.unshift(pat);
					parameters.push(ConstructorPattern(tuple_name(tupleArgs.len()), tupleArgs));
				}
				else
				{
                    //TODO?
				}
			}
		    _ => { break; }
		}
	}
	self.lexer.backtrack();
	return parameters;
}

fn pattern(&mut self) -> Pattern {
	let nameToken = self.lexer.next_();
	match nameToken.token {
	    LBRACKET =>
		{
			if (self.lexer.next_().token != RBRACKET)
			{
				fail!(ParseError(&self.lexer, RBRACKET));
			}
			ConstructorPattern(~"[]", ~[])
		}
	    NAME | OPERATOR =>
		{
			let patterns = self.patternParameter();
			if (nameToken.value.char_at(0).is_uppercase() || nameToken.value == ~":")
			{
				ConstructorPattern(nameToken.value, patterns)
			}
			else
			{
				assert!(patterns.len() == 0);
				IdentifierPattern(nameToken.value)
			}
		}
	    NUMBER => NumberPattern(from_str(nameToken.value).unwrap()),
	    LPARENS =>
		{
			let tupleArgs = self.sepBy1(|this| this.pattern(), COMMA);
			let rParens = self.lexer.current();
			if (rParens.token != RPARENS) {
				fail!(ParseError(&self.lexer, RPARENS));
			}
			ConstructorPattern(tuple_name(tupleArgs.len()), tupleArgs)
		}
	    _ => { fail!("Error parsing pattern") }
	}
}

fn typeDeclaration(&mut self) -> TypeDeclaration {
	let mut typeVariableMapping = HashMap::new();
	self.typeDeclaration_(&typeVariableMapping)
}

fn typeDeclaration_(&mut self, typeVariableMapping : &mut HashMap<~str, TypeVariable>) -> TypeDeclaration {
	let nameToken = self.lexer.next(errorIfNotNameOrLParens);
	let mut name = nameToken.value;
	if (nameToken.token == LPARENS) {
		//Parse a name within parentheses
		let functionName = self.lexer.next(errorIfNotNameOrOperator);
		if (functionName.token != NAME && functionName.token != OPERATOR)
		{
			fail!("Expected NAME or OPERATOR on left side of binding {:?}", functionName.token);
		}
		name = functionName.value;
		let rParens = self.lexer.next(errorIfNotRParens);
		if (rParens.token != RPARENS)
		{
			fail!(ParseError(&self.lexer, RPARENS));
		}
	}
	else if (nameToken.token != NAME) {
		fail!(ParseError(&self.lexer, NAME));
	}
	let decl = self.lexer.next_();
	if (decl.token != TYPEDECL) {
		fail!(ParseError(&self.lexer, TYPEDECL));
	}
	let typeOrContext = self.parse_type_(typeVariableMapping);
	let maybeContextArrow = self.lexer.next_();
	if (maybeContextArrow.token == OPERATOR && maybeContextArrow.value == ~"=>") {
		let t = self.parse_type_(typeVariableMapping);
		let op = match typeOrContext {
            TypeOperator(x) => x,
            _ => fail!("Expected type context since '=>' was parsed")
        };
		return TypeDeclaration { name : name, typ : t, context : createTypeConstraints(op) };
	}
	self.lexer.backtrack();
	TypeDeclaration { name : name, typ : typeOrContext, context : ~[] }
}

fn constructorType(&mut self, arity : &mut int, dataDef : &DataDefinition) -> Type
{
	let token = self.lexer.next(constructorError);
	if (token.token == NAME) {
		*arity += 1;
		if (token.value.char_at(0).is_lowercase())
		{
			match dataDef.parameters.find(&token.value) {
                Some(existingVariable) => { 
                    function_type(existingVariable, &self.constructorType(arity, dataDef))
                }
                None => fail!("Undefined type parameter {:?}", token.value)
            }
		}
		else {
			function_type(&Type::new_op(token.value, ~[]), &self.constructorType(arity, dataDef))
        }
	}
	else {
		TypeOperator(dataDef.typ)
	}
}


fn dataDefinition(&mut self) -> DataDefinition {
	self.requireNext(DATA);
	let dataName = self.requireNext(NAME);

	let mut definition = DataDefinition {
        constructors : ~[],
        typ : TypeOperator { name : dataName.value, types : ~[]},
        parameters : HashMap::new()
    };
	while (self.lexer.next_().token == NAME)
	{
		definition.typ.types.push(Type::new_var(-1));
		definition.parameters.insert(self.lexer.current().value, definition.typ.types[definition.typ.types.len() - 1]);
	}
	let equalToken = self.lexer.current();
	if (equalToken.token != EQUALSSIGN)
	{
		fail!(ParseError(&self.lexer, EQUALSSIGN));
	}
	definition.typ.name = dataName.value;
	definition.constructors = self.sepBy1_func(|this| this.constructor(&definition),
		|t : &Token| t.token == OPERATOR && t.value == ~"|");
	for ii in range(0, definition.constructors.len())
	{
		definition.constructors[ii].tag = ii as int;
	}
	self.lexer.backtrack();
	definition
}


fn parse_type(&mut self) -> Type {
	let mut vars = HashMap::new();
	return self.parse_type_(&mut vars);
}

fn parse_type_(&mut self, typeVariableMapping : &mut HashMap<~str, TypeVariable>) -> Type {
	let result = Type::new_var(0);
	let token = (*self.lexer.next_()).clone();
	match token.token {
	    LBRACKET =>
		{
			let t = self.parse_type_(typeVariableMapping);
			self.requireNext(RBRACKET);
			let args = ~[t];
			let listType = Type::new_op(~"[]", args);
            
            return self.parse_return_type(listType, typeVariableMapping);
		}
	    LPARENS =>
		{
			let t = self.parse_type_(typeVariableMapping);
			let maybeComma = self.lexer.next_().token;
			if (maybeComma == COMMA)
			{
				let mut tupleArgs = self.sepBy1(|this| this.parse_type_(typeVariableMapping), COMMA);
				tupleArgs.unshift(t);
                self.requireNext(RPARENS);

                return self.parse_return_type(tupleType(tupleArgs), typeVariableMapping);
			}
			else if (maybeComma == RPARENS)
			{
                return self.parse_return_type(t, typeVariableMapping);
			}
		}
	    NAME =>
		{
			let mut typeArguments = ~[];
            {
                loop {
                    let next = &self.lexer.next_();
                    if next.token != NAME {
                        break;
                    }
                    let var = typeVariableMapping.find_or_insert(next.value.clone(), TypeVariable { id : -1});
                    typeArguments.push(TypeVariable(*var));
                }
            }
            let next : Token = (*self.lexer.current()).clone();
			let mut thisType = Type::new_var(0);
			if (token.value.char_at(0).is_uppercase())
			{
				thisType = Type::new_op(token.value, typeArguments);
			}
			else
			{
                let t = typeVariableMapping.find_or_insert(token.value, TypeVariable { id : -1});
				thisType = TypeVariable(t.clone());
			}
			return self.parse_return_type(thisType, typeVariableMapping);
		}
	    _ => { return Type::new_var(-1); }
	};
    return Type::new_var(-1);
}

fn parse_return_type(&mut self, typ : Type, typeVariableMapping : &mut HashMap<~str, TypeVariable>) -> Type {

    let arrow = self.lexer.next_().token;
    if (arrow == ARROW) {
        return function_type(&typ, &self.parse_type_(typeVariableMapping));
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
    let mut result = ~[];
    loop {
        result.push(f(self));
        if (sep(self.lexer.next_())) {
            break;
        }
    }
    result
}
}//end impl Parser

fn precedence(s : &str) -> int {
    match s {
        "+" => 1,
        "-" => 1,
        "*" => 3,
        "/" => 3,
        "%" => 3,
        "==" => 1,
        "/=" => 1,
        "<" => 1,
        ">" => 1,
        "<=" => 1,
        ">=" => 1,
        _ => 9
    }
}


fn toplevelError(t : &Token) -> bool
{
	return t.token != NAME
		&& t.token != RBRACKET
		&& t.token != SEMICOLON
		&& t.token != DATA
		&& t.token != LPARENS
		&& t.token != CLASS
		&& t.token != INSTANCE;
}

fn toplevelNewBindError(t : &Token) -> bool
{
	return t.token != RBRACKET
		&& t.token != SEMICOLON;
}

fn bindingError(t : &Token) -> bool
{
	return t.token != EQUALSSIGN
		&& t.token != NAME
		&& t.token != TYPEDECL
		&& t.token != OPERATOR
		&& t.token != RPARENS;
}

fn constructorError(tok : &Token) -> bool
{
	return tok.token != NAME
		&& tok.token != OPERATOR
		&& tok.token != LPARENS;
}

fn tuple_name(size : uint) -> ~str
{
	let mut name = ~"(";
    for _ in range(1, size) {
        name.push_char(',');
    }
	name.push_char(')');
	name
}

fn makeApplication(func : TypedExpr, a : ~[TypedExpr]) -> TypedExpr {
    let mut args = a;
	assert!(args.len() >= 1);
	let mut arg = args.pop();
    let mut ii = args.len() - 1;
	while ii >= 0 {
		arg = TypedExpr::new(Apply(~args.pop(), ~arg));
        ii -= 1;
	}
	TypedExpr::new(Apply(~func, ~arg))
}
fn makeLambda(a : ~[~str], body : TypedExpr) -> TypedExpr {
    let mut args = a;
	assert!(args.len() >= 1);
	let mut body = body;
    let mut ii = args.len() - 1;
	while ii >= 0 {
		body = TypedExpr::new(Lambda(args.pop(), ~body));
        ii -= 1;
	}
    body
}

//Create a tuple with the constructor name inferred from the number of arguments passed in
fn newTuple(arguments : ~[TypedExpr]) -> TypedExpr {
	let name = TypedExpr::new(Identifier(tuple_name(arguments.len())));
	makeApplication(name, arguments)
}

fn subExpressionError(t : &Token) -> bool {
	t.token != LPARENS
		&& t.token != LET
		&& t.token != CASE
		&& t.token != NAME
		&& t.token != NUMBER
		&& t.token != FLOAT
		&& t.token != SEMICOLON
		&& t.token != LBRACKET
}

fn letExpressionEndError(t : &Token) -> bool {
	t.token != IN
}

fn applicationError(t :&Token) -> bool
{
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
		&& t.token != COMMA;
}


fn errorIfNotNameOrLParens(tok : &Token) -> bool {
    tok.token != NAME && tok.token != LPARENS
}
fn errorIfNotIdentifier(tok : &Token) -> bool {
	tok.token != NAME
}
fn errorIfNotNameOrOperator(tok : &Token) -> bool {
	tok.token != NAME && tok.token != OPERATOR
}

fn errorIfNotNameOrEqual(tok : &Token) -> bool {
	tok.token != NAME && tok.token != EQUALSSIGN
}
fn errorIfNotRParens(tok : &Token) -> bool {
	tok.token != RPARENS
}

fn createTypeConstraints(context : TypeOperator) -> ~[TypeOperator] {
	let mut mapping = ~[];

	if (context.name.char_at(0) == '(') {
		for t in context.types.move_iter() {
            let op = match t {
                TypeOperator(op) => op,
                _ => fail!("Expected TypeOperator when creating constraints")
            };
			mapping.push(op);
		}
	}
	else {
		mapping.push(context.clone());
	}
	mapping
}

fn typeParseError(t : &Token) -> bool
{
	return t.token != ARROW
		&& t.token != SEMICOLON
		&& t.token != RBRACE
		&& t.token != RPARENS
		&& t.token != RBRACKET;
}

fn tupleType(types : ~[Type]) -> Type {
	Type::new_op(tuple_name(types.len()), types)
}

fn ParseError<Iter>(lexer : &Lexer<Iter>, expected : TokenEnum) -> ~str {
    format!("Expected {:?}", expected)
}
fn encodeBindingIdentifier(instancename : &str, bindingname : &str) -> ~str {
    fail!("Unimplemented function encodeBinding")
    ~""
}
