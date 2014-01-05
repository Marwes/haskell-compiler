
fn requireNext(expected : Token) -> &Token {
	let tok = self.tokenizer.nextToken();
	if (tok.token != expected) {
		fail!(ParseError(self.tokenizer, expected));
    }
	return tok;
}
    
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


fn module() -> Module {
	let mut module = Module::new();
	let lBracketOrModule = self.tokenizer.tokenizeModule();
	if (lBracketOrModule.token == MODULE)
	{
		let modulename = self.requireNext(NAME);
		module.name = modulename.name;
		self.requireNext(WHERE);
		self.requireNext(LBRACE);
	}
	else if (lBracketOrModule.token == LBRACE)
	{
		//No module declaration was found so default to Main
		module.name = ~"Main";
	}
	else
	{
		fail!(ParseError(self.tokenizer, LBRACE));
	}


	loop {
		//Do a lookahead to see what the next top level binding is
		let token = self.tokenizer.nextToken(toplevelError);
		if (token.token == NAME || token.token == LPARENS)
		{
			let numberOfLookaheads = 2;
			let mut equalOrType = self.tokenizer.nextToken(bindingError);
			while (equalOrType.token != TYPEDECL
				&& equalOrType.token != EQUALSSIGN)
			{
				equalOrType = &self.tokenizer.nextToken(bindingError);
				numberOfLookaheads += 1;
			}
			for _ in range(0, numberOfLookaheads)
			{
				self.tokenizer.backtrack();
			}

			if (equalOrType.token == TYPEDECL)
			{
				let bind = self.tokenDeclaration();
				module.tokenDeclaration.push(bind);
			}
			else
			{
				let bind = self.binding();
				module.bindings.push(bind);
			}
		}
		else if (token.token == CLASS)
		{
			self.tokenizer.backtrack();
			module.classes.push(klass());
		}
		else if (token.token == INSTANCE)
		{
			self.tokenizer.backtrack();
			module.instances.push(instance());
		}
		else if (token.token == DATA)
		{
			self.tokenizer.backtrack();
			module.dataDefinitions.push(dataDefinition());
		}
		else
		{
			break;
		}
		let semicolon = self.tokenizer.nextToken(toplevelNewBindError);
	    if (semicolon.token != SEMICOLON) {
            break;
        }
    }

	let rBracket = self.tokenizer.current();
	if (rBracket.token != RBRACE)
	{
		fail!(ParseError(self.tokenizer, RBRACE));
	}

	let eof = self.tokenizer.nextToken();
	if (none.token != EOF)
	{
		fail!(ParseError("Unexpected token after end of module, {:?}" + self.tokenizer.token));
	}

	for decl in module.tokenDeclaration.iter()
	{
		for bind in module.bindings.iter()
		{
			if (decl.name == bind.name)
			{
				bind.tokenDecl = decl;
			}
		}
	}
    module
}

fn klass() -> Class {
	let klass = Class;

	self.requireNext(CLASS);

	let className = self.requireNext(NAME);
	klass.name = className.name;

	let typeVariable = self.requireNext(NAME);

	self.requireNext(WHERE);
	self.requireNext(LBRACE);
	let typeVariableMapping = HashMap::new();
	typeVariableMapping[typeVariable.name] = klass.variable;
	let decls = self.sepBy1(&Parser::typeDeclaration, typeVariableMapping, SEMICOLON);
	for decl in decls.iter()
	{
		klass.declarations.insert(name, decl);
	}
	
	self.tokenizer.backtrack();
	self.requireNext(RBRACE);

	klass
}

fn instance() -> Instance {
	let inst = Instance;
	self.requireNext(INSTANCE);

	let className = self.requireNext(NAME);
	inst.className = className.name;
	
	inst.tokenDecl = self.parse_type();

	self.requireNext(WHERE);
	self.requireNext(LBRACE);

	inst.bindings = self.sepBy1(&Parser::binding, SEMICOLON);
	for bind in inst.bindings
	{
		bind.name = encodeBindingName(inst.tokenDecl.name, bind.name);
	}

	self.tokenizer.backtrack();
	self.requireNext(RBRACE);
	return inst;
}

fn expression() -> ParsedExpr {
	let app = application();
	parseOperatorExpression(app, 0)
}

fn tupleName(size : uint) -> ~str
{
	let name = str::from_chars([',', ..size]);
	name[0] = '(';
	name[size - 1] = ')';
	return name;
}

fn makeApplication(func : ParsedExpr, args : &[ParsedExpr]) -> ParsedExpr {
	assert!(args.len() >= 1);
	let arg = args[args.len() - 1];
    let ii = args.len() - 2;
	while ii >= 0 {
		arg = newApply(args[ii], arg);
        ii -= 1;
	}
	return newApply(func, arg);
}

//Create a tuple with the constructor name inferred from the number of arguments passed in
fn newTuple(arguments : &[ParsedExpr]) -> ParsedExpr {
	let name = Name(tupleName(arguments.len()));
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

fn parseList(parser : &Parser, tokenizer : &Tokenizer) -> ParsedExpr {
	let expressions = ~[];
	let mut comma;
	loop {
		match parser.expression() {
            Some(expr) => expressions.push(expr),
            None => break
        }
		comma = &self.tokenizer.nextToken();
        if (comma.token != COMMA) {
            break;
        }
	}

	if (expressions.len() == 0)
	{
		return ParsedExpr(Name(~"[]"));
	}

	let application = Number(2);
	{
		let arguments = ~[Variable(2), Variable(2)];
		swap(arguments[0], expressions[expressions.len() - 1]);
		expressions.pop();
		arguments[1] = Name(~"[]");

		application = makeApplication(ParsedExpr(newName(~":")), arguments);
	}
	while (!expressions.empty())
	{
		let arguments = ~[Number(0), Number(0)];//Must be 2 in length
		swap(arguments[0], expressions[expressions.len() - 1]);
		expressions.pop();
		arguments[1] = application;

		application = makeApplication(Name(~":"), arguments);
	}

	let maybeParens = self.tokenizer.current();
	if (maybeParens.token != RBRACKET)
	{
		fail!(ParseError(self.tokenizer, RBRACKET));
	}
	else
	{
		return application;
	}
}

fn subExpression(parseError : |&Token| -> bool) -> ParsedExpr {
	let token = self.tokenizer.nextToken(parseError);
	match token.token {
	    LPARENS =>
		{
			std::vector<ParsedExpr> expressions = self.sepBy1(&Parser::expression, COMMA);

			let maybeParens = self.tokenizer.current();

			if (maybeParens.token != RPARENS)
			{
				fail!(ParseError(self.tokenizer, RPARENS));
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
	    LBRACKET => parseList(*this, self.tokenizer),
	    LET =>
		{
			self.requireNext(LBRACE);

			let binds = self.sepBy1(&Parser::binding, SEMICOLON);

			let rBracket = self.tokenizer.current();
			if (rBracket.token != RBRACE)
			{
				fail!(ParseError(self.tokenizer, RBRACE));
			}
			let inToken = self.tokenizer.nextToken(letExpressionEndError);
			if (inToken.token != IN) {
				fail!(ParseError(self.tokenizer, IN));
            }
			return ParsedExpr(newLet(binds.size, expression()));
		}
	    CASE =>
		{
			let expr = expression();

			self.requireNext(OF);
			self.requireNext(LBRACE);

			let alts = self.sepBy1(&Parser::alternative, SEMICOLON);
			let rBrace = self.tokenizer.current();
			if (rBrace.token != RBRACE)
			{
				fail!(ParseError(self.tokenizer, RBRACE));
			}
			return ParsedExpr(Case(expr, alts), token.location);
		}
        NAME => ParsedExpr(Name(token.name), token.location),
        NUMBER => ParsedExpr(Number(token.name.from_str()), token.location),
	    FLOAT => ParsedExpr(Rational(token.name.from_str()), token.location),
	    _ => {
		self.tokenizer.backtrack();
        None
        }
    }
}

fn alternative() -> Alternative {
	let pat = pattern();

	self.requireNext(ARROW);

	Alternative(pat, expression())
}

fn parseOperatorExpression(lhs : ParsedExpr, minPrecedence : int) -> ParsedExpr {
	self.tokenizer.nextToken();
	let f = self.tokenizer.current();
	while (self.tokenizer.valid() && self.tokenizer.token == OPERATOR
		&& prrecedence(self.tokenizer.name) >= minPrecedence)
	{
		let op = self.tokenizer.current();
		let rhs = application();
		let nextOP = self.tokenizer.nextToken();
		while (self.tokenizer && nextOP.token == OPERATOR
			&& precedence(nextOP.name) > precedence(op.name))
		{
			let lookahead = self.tokenizer.current();
			self.tokenizer.backtrack();
			rhs = parseOperatorExpression(rhs, getPrecedence(lookahead.name));
			self.tokenizer.nextToken();
		}
		if (rhs == None && lhs == None)
		{
			return None;
		}
		let name = Name(op.name, op.location);
		let args = if lhs == None { 1 } else { 2 };
		let loc = if lhs == None { op.location } else { lhs.location};
		if (rhs == None)
		{
			let args = ~[lhs, ParsedExpr(Name("#", loc))];
			let apply = ParsedExpr(Apply(name, args), loc);
			std::vector<std::string> params(1);
			params[0] = "#";
			lhs = ParsedExpr(Lambda(params, apply), loc);
		}
		else if (lhs == nullptr)
		{
			if (op.name == "-")
			{
				name.name = ~"negate";
				args[0] = rhs;
				lhs = ParsedExpr(Apply(name, args), loc);
			}
			else
			{
				let args = ~[Name("#", loc), rhs];
				let apply = Apply(name, args, loc);
				let params = ~[~"#"];
				lhs = ParsedExpr(Lambda(params, apply), loc);
			}
		}
		else
		{
			args[0] = lhs;
			args[1] = rhs;
			lhs = ParsedExpr(Apply(name, args), loc);
		}
	}
	self.tokenizer.backtrack();
	lhs
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

fn application() -> ParsedExpr {
	let lhs = subExpression();
	if (lhs == None) {
		return None;
    }

	let mut expressions = ~[];
	loop {
        let expr = subExpression(applicationError);
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


fn errorIfNotNameOrLParens(tok : &Token) -> bool
{
	return tok.token != NAME
		&& tok.token != LPARENS;
}
fn errorIfNotName(tok : &Token) -> bool
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

fn binding() -> ParsedBinding {
	//name1 = expr
	//or
	//name2 x y = expr
	let nameToken = self.tokenizer.nextToken(errorIfNotNameOrLParens);
	let name = nameToken.name;
	if (nameToken.token == LPARENS)
	{
		//Parse a name within parentheses
		let functionName = self.tokenizer.nextToken(errorIfNotNameOrOperator);
		if (functionName.token != NAME && functionName.token != OPERATOR)
		{
			fail!("Expected NAME or OPERATOR on left side of binding {:?}", functionName.token);
		}
		name = functionName.name;
		let rParens = self.tokenizer.nextToken(errorIfNotRParens);
		if (rParens.token != RPARENS)
		{
			fail!(ParseError(self.tokenizer, RPARENS));
		}
	}
	else if (nameToken.token != NAME)
	{
		fail!(ParseError(self.tokenizer, NAME));
	}

	//Parse the arguments for the binding
	let mut arguments = ~[];
	while (true)
	{
		let token = self.tokenizer.nextToken(errorIfNotNameOrEqual);
		if (token.token == NAME)
		{
			arguments.push(token.name);
		}
		else
		{
			break;
		}
	}
	if (self.tokenizer.current().token != EQUALSSIGN)
	{
		fail!(ParseError(self.tokenizer, EQUALSSIGN));
	}
	if (arguments.len() > 0)
    {
		let mut argnames = ~[];
		for a in arguments {
			argnames.push(a.c_str());
        }
		let lambda = Lambda(arguments, expression());
		return Binding::new(name, lambda);
	}
	else
	{
		return Binding::new(name, expression());
	}
}


fn patternParameter() -> ~[Pattern] {
	let mut parameters = ~[];
	loop {
		let token = self.tokenizer.nextToken();
		match token.token
		{
            NAME => parameters.push(NamePattern(token.name)),
            NUMBER => parameters.push(NumberPattern(token.name.from_str())),
		    LPARENS =>
			{
				let pat = pattern();
				let maybeComma = self.tokenizer.nextToken();
				if (maybeComma.token == COMMA)
				{
					let tupleArgs = self.sepBy1(&Parser::pattern, COMMA);
					let rParens = self.tokenizer.current();
					if (rParens.token != RPARENS)
					{
						fail!(ParseError(self.tokenizer, RPARENS));
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
	self.tokenizer.backtrack();
	return parameters;
}

fn pattern() -> Pattern {
	let nameToken = self.tokenizer.nextToken();
	match nameToken.token {
	    LBRACKET =>
		{
			if (self.tokenizer.nextToken().token != RBRACKET)
			{
				fail!(ParseError(self.tokenizer, RBRACKET));
			}
			return ConstructorPattern("[]", ~[]);
		}
	    NAME | OPERATOR =>
		{
			std::vector<std::unique_ptr<Pattern>> patterns = patternParameter();
			if (isupper(nameToken.name[0]) || nameToken.name == ":")
			{
				return ConstructorPattern(nameToken.name, patterns);
			}
			else
			{
				assert!(patterns.len() == 0);
				return PatternName(nameToken.name);
			}
		}
	    NUMBER => NumberLiteral(nameToken.name.from_str()),
	    LPARENS =>
		{
			let tupleArgs = self.sepBy1(&Parser::pattern, COMMA);
			let rParens = self.tokenizer.current();
			if (rParens.token != RPARENS) {
				fail!(ParseError(self.tokenizer, RPARENS));
			}
			return ConstructorPattern(tupleName(tupleArgs.len()), tupleArgs);
		}
	    _ => { break; }
	}
	return None;//fail?
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

fn typeDeclaration() -> TypeDeclaration {
	let typeVariableMapping = HashMap::new();
	self.typeDeclaration_(typeVariableMapping)
}

fn typeDeclaration(typeVariableMapping : &mut HashMap<~str, TypeVariable>) -> TypeDeclaration {
	let nameToken = self.tokenizer.nextToken(errorIfNotNameOrLParens);
	let name = nameToken.name;
	if (nameToken.token == LPARENS) {
		//Parse a name within parentheses
		let functionName = self.tokenizer.nextToken(errorIfNotNameOrOperator);
		if (functionName.token != NAME && functionName.token != OPERATOR)
		{
			fail!("Expected NAME or OPERATOR on left side of binding {:?}", functionName.token);
		}
		name = functionName.name;
		let rParens = self.tokenizer.nextToken(errorIfNotRParens);
		if (rParens.token != RPARENS)
		{
			fail!(ParseError(self.tokenizer, RPARENS));
		}
	}
	else if (nameToken.token != NAME) {
		fail!(ParseError(self.tokenizer, NAME));
	}
	let decl = self.tokenizer.nextToken();
	if (decl.token != TYPEDECL) {
		fail!(ParseError(self.tokenizer, TYPEDECL));
	}
	let typeOrContext = self.parse_type(typeVariableMapping);
	let maybeContextArrow = self.tokenizer.nextToken();
	if (maybeContextArrow.token == OPERATOR && maybeContextArrow.name == "=>") {
		let t = self.parse_type(typeVariableMapping);
		let op = boost::get<TypeOperator>(typeOrContext);
		return TypeDeclaration(name, t, createTypeConstraints(op));
	}
	self.tokenizer.backtrack();
	TypeDeclaration(name, typeOrContext)
}

fn constructorError(tok : &Token) -> bool
{
	return tok.token != NAME
		&& tok.token != OPERATOR
		&& tok.token != LPARENS;
}

fn constructorType(tokenizer : &Tokenizer, arity : &mut int, dataDef : &DataDefinition) -> Type
{
	let token = self.tokenizer.nextToken(constructorError);
	if (token.token == NAME) {
		arity += 1;
		if (token.name[0].is_lowercase())
		{
			match dataDef.parameters.find(token.name) {
                Some(existingVariable) => { 
                    functionType(existingVariable, constructorType(self.tokenizer, arity, dataDef))
                }
                None => fail!("Undefined type parameter {:?}", token.name)
            }
		}
		else {
			functionType(TypeOperator(token.name), constructorType(self.tokenizer, arity, dataDef));
        }
	}
	else {
		dataDef.token
	}
}

fn constructor(dataDef : &DataDefinition) -> Constructor {
	let nameToken = self.tokenizer.nextToken();
	let arity = 0;
	let typ = constructorType(self.tokenizer, arity, dataDef);
	self.tokenizer.backtrack();
	Constructor(nameToken.name, typ, 0, arity)
}

fn dataDefinition() -> DataDefinition {
	self.requireNext(DATA);
	let dataName = self.requireNext(NAME);

	let mut definition = DataDefinition;
	definition.token = TypeOperator(dataName.name);
	let op = boost::get<TypeOperator>(definition.token);
	while (self.tokenizer.nextToken().token == NAME)
	{
		definition.token.types.push(TypeVariable());
		definition.parameters.insert(self.tokenizer.name, definition.token.types[definition.token.types.len() - 1]);
	}
	let equalToken = self.tokenizer.current();
	if (equalToken.token != EQUALSSIGN)
	{
		fail!(ParseError(self.tokenizer, EQUALSSIGN));
	}
	definition.name = dataName.name;
	definition.constructors = self.sepBy1(&Parser::constructor, definition,
		|t : &Token| t.token == OPERATOR && t.name == "|");
	for ii in range(0, definition.constructors.len())
	{
		definition.constructors[ii].tag = ii;
	}
	self.tokenizer.backtrack();
	definition
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
	TypeOperator(tupleName(types.len()), types)
}

fn parse_type() -> Type {
	let mut vars = HashMap::new();
	return self.parse_type(&vars);
}
fn parse_type(typeVariableMapping : &mut HashMap<~str, TypeVariable>) -> Type {
	let result = TypeVariable(0);
	let token = self.tokenizer.nextToken();
	match token.token {
	    LBRACKET =>
		{
			let t = self.parse_type(typeVariableMapping);
			self.requireNext(RBRACKET);
			let args = ~[t];
			let listType = TypeOperator("[]", args);

			let arrow = self.tokenizer.nextToken();
			if (arrow.token == ARROW) {
				functionType(listType, self.parse_type(typeVariableMapping));
			}
            else {
                self.tokenizer.backtrack();
                listType
            }
		}
	    LPARENS =>
		{
			let t = self.parse_type(typeVariableMapping);
			let maybeComma = self.tokenizer.nextToken();
			if (maybeComma.token == COMMA)
			{
				let tupleArgs = self.sepBy1(&Parser::parse_type, typeVariableMapping, COMMA);
				tupleArgs.insert(tupleArgs.begin(), t);
				let rParens = self.tokenizer.current();
				if (rParens.token != RPARENS)
				{
					fail!(ParseError(self.tokenizer, RPARENS));
				}
				let arrow = self.tokenizer.nextToken();
				if (arrow.token == ARROW) {
					functionType(tupleType(tupleArgs), self.parse_type(typeVariableMapping));
				}
                else {
				    self.tokenizer.backtrack();
				    tupleType(tupleArgs);
                }
			}
			else if (maybeComma.token == RPARENS)
			{
				let arrow = self.tokenizer.nextToken();
				if (arrow.token == ARROW) {
					return functionType(t, self.parse_type(typeVariableMapping));
                }
				else {
					self.tokenizer.backtrack();
					t
				}
			}
		}
	    NAME =>
		{
			let next = self.tokenizer.nextToken();
			let typeArguments = ~[];
			while next.token == NAME
			{
				if (typeVariableMapping.key.key_exists(next.name))
				{
					typeVariableMapping[next.name] = TypeVariable();
				}
				typeArguments.push(typeVariableMapping[next.name]);
				next = &self.tokenizer.nextToken();
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
				thisType = functionType(thisType, self.parse_type(typeVariableMapping));
			}
			else {
				self.tokenizer.backtrack();
			}
			return thisType;
		}
	    _ => { TypeVariable() }
	}
}


