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
    typeDecl : TypeDeclaration,
    classname : ~str
}

struct Binding {
    name : ~str,
    expression : TypedExpr
}

struct Constructor {
    name : ~str,
    typ : Type,
    tag : int,
    arity : int
}

struct DataDefinition {
    constructors : ~[Constructor],
    typ : TypeOperator
}

struct TypeDeclaration {
    context : Option<()>,
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

struct Parser {
    lexer : Lexer,
}

impl Parser {

fn requireNext(&mut self, expected : Token) -> &Token {
	let tok = self.lexer.nextToken();
	if (tok.token != expected) {
		fail!(ParseError(self.lexer, expected));
    }
	return tok;
}

fn module(&mut self) -> Module {
	let lBracketOrModule = self.lexer.tokenizeModule();
	let modulename = match lBracketOrModule.token {
        MODULE => {
            let modulename = self.requireNext(NAME);
            self.requireNext(WHERE);
            self.requireNext(LBRACE);
            modulename.name
	    }
        LBRACE => {
		    //No module declaration was found so default to Main
		    ~"Main"
	    }
        _ => fail!(ParseError(self.lexer, LBRACE))
    };

    let mut classes = ~[];
    let mut bindings = ~[];
    let mut instances = ~[];
    let mut typeDeclarations = ~[];
    let mut dataDefinitions = ~[];
	loop {
		//Do a lookahead to see what the next top level binding is
		let token = self.lexer.nextToken(toplevelError);
		if (token.token == NAME || token.token == LPARENS)
		{
			let numberOfLookaheads = 2;
			let mut equalOrType = self.lexer.nextToken(bindingError);
			while (equalOrType.token != TYPEDECL
				&& equalOrType.token != EQUALSSIGN)
			{
				equalOrType = &self.lexer.nextToken(bindingError);
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
		let semicolon = self.lexer.nextToken(toplevelNewBindError);
	    if (semicolon.token != SEMICOLON) {
            break;
        }
    }

	let rBracket = self.lexer.current();
	if (rBracket.token != RBRACE)
	{
		fail!(ParseError(self.lexer, RBRACE));
	}

	let eof = self.lexer.nextToken();
	if (eof.token != EOF)
	{
		fail!(ParseError("Unexpected token after end of module, {:?}" + self.lexer.token));
	}

	for decl in typeDeclarations.iter()
	{
		for bind in bindings.iter()
		{
			if (decl.name == bind.name)
			{
				bind.typeDecl = decl;
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
	let typeVariable = self.requireNext(NAME).value;

	self.requireNext(WHERE);
	self.requireNext(LBRACE);
	let typeVariableMapping = HashMap::new();
	typeVariableMapping[typeVariable] = typeVariable;
	let declarations = self.sepBy1(&Parser::typeDeclaration_, typeVariableMapping, SEMICOLON);
	
	self.lexer.backtrack();
	self.requireNext(RBRACE);

	Class { name : classname, declarations : declarations }
}

fn instance(&mut self) -> Instance {
	self.requireNext(INSTANCE);

	let classname = self.requireNext(NAME).value;
	
	let typeDecl = self.parse_type();

	self.requireNext(WHERE);
	self.requireNext(LBRACE);

	let mut bindings = self.sepBy1(&Parser::binding, SEMICOLON);
	for bind in bindings
	{
		bind.name = encodeBindingIdentifier(typeDecl.name, bind.name);
	}

	self.lexer.backtrack();
	self.requireNext(RBRACE);
	Instance { typeDecl : typeDecl, classname : classname, bindings : bindings }
}

fn expression(&mut self) -> TypedExpr {
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
		comma = &self.lexer.nextToken();
        if (comma.token != COMMA) {
            break;
        }
	}

	if (expressions.len() == 0)
	{
		return TypedExpr::new(Identifier(~"[]"));
	}

	let application = Number(2);
	{
		let arguments = ~[TypeVariable(2), TypeVariable(2)];
		swap(arguments[0], expressions[expressions.len() - 1]);
		expressions.pop();
		arguments[1] = Identifier(~"[]");

		application = makeApplication(TypedExpr::new(Identifier(~":")), arguments);
	}
	while (!expressions.empty())
	{
		let arguments = ~[Number(0), Number(0)];//Must be 2 in length
		swap(arguments[0], expressions[expressions.len() - 1]);
		expressions.pop();
		arguments[1] = application;

		application = makeApplication(Identifier(~":"), arguments);
	}

	let maybeParens = self.lexer.current();
	if (maybeParens.token != RBRACKET)
	{
		fail!(ParseError(self.lexer, RBRACKET));
	}
	else
	{
		return application;
	}
}

fn subExpression(&mut self, parseError : |&Token| -> bool) -> TypedExpr {
	let token = self.lexer.nextToken(parseError);
	match token.token {
	    LPARENS =>
		{
			let expressions = self.sepBy1(&Parser::expression, COMMA);

			let maybeParens = self.lexer.current();

			if (maybeParens.token != RPARENS)
			{
				fail!(ParseError(self.lexer, RPARENS));
			}
			if (expressions.len() == 1)
			{
				return expressions[0];
			}
			else
			{
				return newTuple(expressions);
			}
		}
	    LBRACKET => self.parseList(),
	    LET =>
		{
			self.requireNext(LBRACE);

			let binds = self.sepBy1(&Parser::binding, SEMICOLON);

			let rBracket = self.lexer.current();
			if (rBracket.token != RBRACE)
			{
				fail!(ParseError(self.lexer, RBRACE));
			}
			let inToken = self.lexer.nextToken(letExpressionEndError);
			if (inToken.token != IN) {
				fail!(ParseError(self.lexer, IN));
            }
			return TypedExpr::new(Let(binds.size, self.expression()));
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
				fail!(ParseError(self.lexer, RBRACE));
			}
			return TypedExpr::with_location(Case(expr, alts), token.location);
		}*/
        NAME => TypedExpr::with_location(Identifier(token.name), token.location),
        NUMBER => TypedExpr::with_location(Number(token.name.from_str()), token.location),
	    //FLOAT => TypedExpr::with_location(Rational(token.name.from_str()), token.location),
	    _ => {
		self.lexer.backtrack();
        None
        }
    }
}

fn alternative(&mut self) -> Alternative {
	let pat = self.pattern();

	self.requireNext(ARROW);

	Alternative { pattern : pat, expression : self.expression() }
}

fn parseOperatorExpression(&mut self, lhs : TypedExpr, minPrecedence : int) -> TypedExpr {
	self.lexer.nextToken();
	let f = self.lexer.current();
	while (self.lexer.valid() && self.lexer.token == OPERATOR
		&& precedence(self.lexer.name) >= minPrecedence)
	{
		let op = self.lexer.current();
		let rhs = self.application();
		let nextOP = self.lexer.nextToken();
		while (self.lexer && nextOP.token == OPERATOR
			&& precedence(nextOP.name) > precedence(op.name))
		{
			let lookahead = self.lexer.current();
			self.lexer.backtrack();
			rhs = self.parseOperatorExpression(rhs, precedence(lookahead.name));
			self.lexer.nextToken();
		}
		if (rhs == None && lhs == None)
		{
			return None;
		}
		let name = Identifier(op.name, op.location);
		let args = if lhs == None { 1 } else { 2 };
		let loc = if lhs == None { op.location } else { lhs.location};
		if (rhs == None)
		{
			let args = ~[lhs, TypedExpr::with_location(Identifier("#", loc))];
			let apply = TypedExpr::with_location(Apply(name, args), loc);
			let params = ~[~"#"];
			lhs = TypedExpr::with_location(Lambda(params, apply), loc);
		}
		else if (lhs == None)
		{
			if (op.name == "-")
			{
				name.name = ~"negate";
				args[0] = rhs;
				lhs = TypedExpr::with_location(Apply(name, args), loc);
			}
			else
			{
				let args = ~[Identifier("#", loc), rhs];
				let apply = Apply(name, args, loc);
				let params = ~[~"#"];
				lhs = TypedExpr::with_location(Lambda(params, apply), loc);
			}
		}
		else
		{
			args[0] = lhs;
			args[1] = rhs;
			lhs = TypedExpr::with_location(Apply(name, args), loc);
		}
	}
	self.lexer.backtrack();
	lhs
}

fn application(&mut self) -> TypedExpr {
	let lhs = self.subExpression();
	if (lhs == None) {
		return None;
    }

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
		lhs = Apply(lhs, expressions, loc);
	}
    lhs
}

fn constructor(&mut self, dataDef : &DataDefinition) -> Constructor {
	let nameToken = self.lexer.nextToken();
	let arity = 0;
	let typ = self.constructorType(self.lexer, arity, dataDef);
	self.lexer.backtrack();
	Constructor { name : nameToken.name, typ : typ, tag : 0, arity : arity }
}

fn binding(&mut self) -> Binding {
	//name1 = expr
	//or
	//name2 x y = expr
	let nameToken = self.lexer.nextToken(errorIfNotNameOrLParens);
	let name = nameToken.name;
	if (nameToken.token == LPARENS)
	{
		//Parse a name within parentheses
		let functionName = self.lexer.nextToken(errorIfNotNameOrOperator);
		if (functionName.token != NAME && functionName.token != OPERATOR)
		{
			fail!("Expected NAME or OPERATOR on left side of binding {:?}", functionName.token);
		}
		name = functionName.name;
		let rParens = self.lexer.nextToken(errorIfNotRParens);
		if (rParens.token != RPARENS)
		{
			fail!(ParseError(self.lexer, RPARENS));
		}
	}
	else if (nameToken.token != NAME)
	{
		fail!(ParseError(self.lexer, NAME));
	}

	//Parse the arguments for the binding
	let mut arguments = ~[];
	while (true)
	{
		let token = self.lexer.nextToken(errorIfNotNameOrEqual);
		if (token.token == NAME)
		{
			arguments.push(token.name);
		}
		else
		{
			break;
		}
	}
	if (self.lexer.current().token != EQUALSSIGN)
	{
		fail!(ParseError(self.lexer, EQUALSSIGN));
	}
	if (arguments.len() > 0)
    {
		let mut argnames = ~[];
		for a in arguments {
			argnames.push(a.c_str());
        }
		let lambda = Lambda(arguments, self.expression());
		return Binding { name : name, expression : lambda };
	}
	else
	{
		return Binding { name : name, expression : self.expression() };
	}
}


fn patternParameter(&mut self) -> ~[Pattern] {
	let mut parameters = ~[];
	loop {
		let token = self.lexer.nextToken();
		match token.token
		{
            NAME => parameters.push(IdentifierPattern(token.name)),
            NUMBER => parameters.push(NumberPattern(token.name.from_str())),
		    LPARENS =>
			{
				let pat = self.pattern();
				let maybeComma = self.lexer.nextToken();
				if (maybeComma.token == COMMA)
				{
					let tupleArgs = self.sepBy1(&Parser::pattern, COMMA);
					let rParens = self.lexer.current();
					if (rParens.token != RPARENS)
					{
						fail!(ParseError(self.lexer, RPARENS));
					}
					tupleArgs.unshift(pat);
					parameters.push(ConstructorPattern(tupleArgs));
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
	let nameToken = self.lexer.nextToken();
	match nameToken.token {
	    LBRACKET =>
		{
			if (self.lexer.nextToken().token != RBRACKET)
			{
				fail!(ParseError(self.lexer, RBRACKET));
			}
			return ConstructorPattern("[]", ~[]);
		}
	    NAME | OPERATOR =>
		{
			let patterns = self.patternParameter();
			if (nameToken.name[0].is_uppercase() || nameToken.name == ":")
			{
				return ConstructorPattern(nameToken.name, patterns);
			}
			else
			{
				assert!(patterns.len() == 0);
				return IdentifierPattern(nameToken.name);
			}
		}
	    NUMBER => NumberPattern(nameToken.name.from_str()),
	    LPARENS =>
		{
			let tupleArgs = self.sepBy1(&Parser::pattern, COMMA);
			let rParens = self.lexer.current();
			if (rParens.token != RPARENS) {
				fail!(ParseError(self.lexer, RPARENS));
			}
			return ConstructorPattern(tuple_name(tupleArgs.len()), tupleArgs);
		}
	    _ => { break; }
	}
	return None;//fail?
}

fn typeDeclaration(&mut self) -> TypeDeclaration {
	let typeVariableMapping = HashMap::new();
	self.typeDeclaration_(typeVariableMapping)
}

fn typeDeclaration_(&mut self, typeVariableMapping : &mut HashMap<~str, TypeVariable>) -> TypeDeclaration {
	let nameToken = self.lexer.nextToken(errorIfNotNameOrLParens);
	let name = nameToken.name;
	if (nameToken.token == LPARENS) {
		//Parse a name within parentheses
		let functionName = self.lexer.nextToken(errorIfNotNameOrOperator);
		if (functionName.token != NAME && functionName.token != OPERATOR)
		{
			fail!("Expected NAME or OPERATOR on left side of binding {:?}", functionName.token);
		}
		name = functionName.name;
		let rParens = self.lexer.nextToken(errorIfNotRParens);
		if (rParens.token != RPARENS)
		{
			fail!(ParseError(self.lexer, RPARENS));
		}
	}
	else if (nameToken.token != NAME) {
		fail!(ParseError(self.lexer, NAME));
	}
	let decl = self.lexer.nextToken();
	if (decl.token != TYPEDECL) {
		fail!(ParseError(self.lexer, TYPEDECL));
	}
	let typeOrContext = self.parse_type(typeVariableMapping);
	let maybeContextArrow = self.lexer.nextToken();
	if (maybeContextArrow.token == OPERATOR && maybeContextArrow.name == "=>") {
		let t = self.parse_type(typeVariableMapping);
		let op = match typeOrContext {
            TypeOperator(x) => x,
            _ => fail!("Expected type context since '=>' was parsed")
        };
		return TypeDeclaration { name : name, typ : t, context : createTypeConstraints(op) };
	}
	self.lexer.backtrack();
	TypeDeclaration { name : name, typ : typeOrContext, context : None }
}

fn constructorType(&mut self, arity : &mut int, dataDef : &DataDefinition) -> Type
{
	let token = self.lexer.nextToken(constructorError);
	if (token.token == NAME) {
		arity += 1;
		if (token.name[0].is_lowercase())
		{
			match dataDef.parameters.find(token.name) {
                Some(existingVariable) => { 
                    function_type(existingVariable, self.constructorType(self.lexer, arity, dataDef))
                }
                None => fail!("Undefined type parameter {:?}", token.name)
            }
		}
		else {
			function_type(TypeOperator(token.name), self.constructorType(self.lexer, arity, dataDef));
        }
	}
	else {
		dataDef.token
	}
}


fn dataDefinition(&mut self) -> DataDefinition {
	self.requireNext(DATA);
	let dataName = self.requireNext(NAME);

	let mut definition = DataDefinition {
        constructors : ~[],
        typ : TypeOperator { name : dataName.name, types : ~[] }
    };
	while (self.lexer.nextToken().token == NAME)
	{
		definition.typ.types.push(TypeVariable());
		definition.parameters.insert(self.lexer.name, definition.token.types[definition.token.types.len() - 1]);
	}
	let equalToken = self.lexer.current();
	if (equalToken.token != EQUALSSIGN)
	{
		fail!(ParseError(self.lexer, EQUALSSIGN));
	}
	definition.name = dataName.name;
	definition.constructors = self.sepBy1(&Parser::constructor, definition,
		|t : &Token| t.token == OPERATOR && t.name == "|");
	for ii in range(0, definition.constructors.len())
	{
		definition.constructors[ii].tag = ii;
	}
	self.lexer.backtrack();
	definition
}


fn parse_type(&mut self) -> Type {
	let mut vars = HashMap::new();
	return self.parse_type(&vars);
}

fn parse_type_(&mut self, typeVariableMapping : &mut HashMap<~str, TypeVariable>) -> Type {
	let result = TypeVariable(0);
	let token = self.lexer.nextToken();
	match token.token {
	    LBRACKET =>
		{
			let t = self.parse_type_(typeVariableMapping);
			self.requireNext(RBRACKET);
			let args = ~[t];
			let listType = TypeOperator("[]", args);

			let arrow = self.lexer.nextToken();
			if (arrow.token == ARROW) {
				function_type(listType, self.parse_type_(typeVariableMapping));
			}
            else {
                self.lexer.backtrack();
                listType
            }
		}
	    LPARENS =>
		{
			let t = self.parse_type_(typeVariableMapping);
			let maybeComma = self.lexer.nextToken();
			if (maybeComma.token == COMMA)
			{
				let tupleArgs = self.sepBy1(&Parser::parse_type, typeVariableMapping, COMMA);
				tupleArgs.insert(tupleArgs.begin(), t);
				let rParens = self.lexer.current();
				if (rParens.token != RPARENS)
				{
					fail!(ParseError(self.lexer, RPARENS));
				}
				let arrow = self.lexer.nextToken();
				if (arrow.token == ARROW) {
					function_type(tupleType(tupleArgs), self.parse_type(typeVariableMapping));
				}
                else {
				    self.lexer.backtrack();
				    tupleType(tupleArgs);
                }
			}
			else if (maybeComma.token == RPARENS)
			{
				let arrow = self.lexer.nextToken();
				if (arrow.token == ARROW) {
					return function_type(t, self.parse_type(typeVariableMapping));
                }
				else {
					self.lexer.backtrack();
					t
				}
			}
		}
	    NAME =>
		{
			let next = self.lexer.nextToken();
			let typeArguments = ~[];
			while next.token == NAME
			{
				if (typeVariableMapping.key.key_exists(next.name))
				{
					typeVariableMapping[next.name] = TypeVariable();
				}
				typeArguments.push(typeVariableMapping[next.name]);
				next = &self.lexer.nextToken();
			}
			let mut thisType = TypeVariable(0);
			if (token.name[0].is_uppercase())
			{
				thisType = TypeOperator(token.name, typeArguments);
			}
			else
			{
				thisType = typeVariableMapping.find_or_insert(token.name, token.name, TypeVariable());
			}
			if (next.token == ARROW) {
				thisType = function_type(thisType, self.parse_type_(typeVariableMapping));
			}
			else {
				self.lexer.backtrack();
			}
			return thisType;
		}
	    _ => { TypeVariable() }
	}
}

}//end impl Parser

fn isPlusMinusOP(token : &Token) -> bool
{
    return token.token == OPERATOR && (token.name == "+" || token.name == "-");
}

fn isMultDivOp(token : &Token) -> bool
{
    return token.token == OPERATOR && (token.name == "*" || token.name == "/" || token.name == "%");
}

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
	let name = from_chars([',', ..size]);
	name[0] = '(';
	name[size - 1] = ')';
	return name;
}

fn makeApplication(func : TypedExpr, args : &[TypedExpr]) -> TypedExpr {
	assert!(args.len() >= 1);
	let arg = args[args.len() - 1];
    let ii = args.len() - 2;
	while ii >= 0 {
		arg = Apply(args[ii], arg);
        ii -= 1;
	}
	return Apply(func, arg);
}

//Create a tuple with the constructor name inferred from the number of arguments passed in
fn newTuple(arguments : &[TypedExpr]) -> TypedExpr {
	let name = Identifier(tuple_name(arguments.len()));
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


fn errorIfNotNameOrLParens(tok : &Token) -> bool
{
	return tok.token != NAME
		&& tok.token != LPARENS;
}
fn errorIfNotIdentifier(tok : &Token) -> bool
{
	return tok.token != NAME;
}
fn errorIfNotNameOrOperator(tok : &Token) -> bool
{
	return tok.token != NAME
		&& tok.token != OPERATOR;
}

fn errorIfNotNameOrEqual(tok : &Token)
{
	return tok.token != NAME && tok.token != EQUALSSIGN;
}
fn errorIfNotRParens(tok : &Token)
{
	return tok.token != RPARENS;
}

fn createTypeConstraints(context : &TypeOperator) -> ~[TypeOperator] {
	let mapping = ~[];

	if (context.name[0] == '(') {
		for t in context.tokens {
			mapping.push(t);//match TypeOperator
		}
	}
	else {
		mapping.push(context);
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

fn tupleType(types : ~&[Type]) -> Type {
	TypeOperator(tuple_name(types.len()), types)
}

fn ParseError(lexer : &Lexer, expected : TokenEnum) -> ~str {
    format!("Expected {:?}", expected)
}
fn encodeBindingIdentifier(instancename : &str, bindingname : &str) -> ~str {
    fail!("Unimplemented function encodeBinding")
    ~""
}
