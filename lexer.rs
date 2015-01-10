use std::fmt;
use std::collections::RingBuf;
use std::iter::Peekable;
use std::rc::Rc;
use std::cell::RefCell;
use interner::*;

use self::TokenEnum::*;

#[deriving(Clone, PartialEq, Show)]
pub enum TokenEnum {
	EOF,
	NAME,
	OPERATOR,
	NUMBER,
	FLOAT,
    STRING,
    CHAR,
	LPARENS,
	RPARENS,
	LBRACKET,
	RBRACKET,
	LBRACE,
	RBRACE,
	INDENTSTART,
	INDENTLEVEL,
	COMMA,
    PIPE,
    CONTEXTARROW,
	EQUALSSIGN,
	SEMICOLON,
	MODULE,
	CLASS,
	INSTANCE,
	WHERE,
	LET,
	IN,
	CASE,
	OF,
	ARROW,
    LARROW,
	TYPEDECL,
	DATA,
    NEWTYPE,
    LAMBDA,
    DO,
    IMPORT,
    INFIXL,
    INFIXR,
    INFIX,
    DERIVING,
    IF,
    THEN,
    ELSE
}

#[deriving(Clone, PartialEq)]
pub struct Location {
    pub column : int,
    pub row : int,
    pub absolute : int
}

impl Location {
    pub fn eof() -> Location {
        Location { column: -1, row: -1, absolute: -1 }
    }
}
#[deriving(Clone)]
pub struct Located<T> {
    pub location: Location,
    pub node: T
}

impl <T: PartialEq> PartialEq for Located<T> {
    fn eq(&self, o: &Located<T>) -> bool {
        self.node == o.node
    }
}
    
impl <T: fmt::Show> fmt::Show for Located<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.node)
    }
}

impl fmt::Show for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.row, self.column)
    }
}

#[deriving(Clone, Show)]
pub struct Token {
    pub token : TokenEnum,
    pub value : InternedStr,
    pub location : Location
}
impl Token {
    fn eof() -> Token {
        Token { token : EOF, value : intern(""), location : Location { column : -1, row : -1, absolute : -1} }
    }

    fn new(interner: &Rc<RefCell<Interner>>, token : TokenEnum, value : &str, loc : Location) -> Token {
        Token { token: token, value: (**interner).borrow_mut().intern(value), location: loc }
    }

    #[cfg(test)]
    fn new_(token : TokenEnum, value : &str) -> Token {
        Token::new(&get_local_interner(), token, value, Location { column : -1, row : -1, absolute : -1 })
    }
}

impl PartialEq for Token {
    fn eq(&self, rhs : &Token) -> bool {
        self.token == rhs.token && self.value == rhs.value
    }
}

///Takes a string which can be an identifier or a keyword and returns the correct TokenEnum
fn name_or_keyword(tok : &str) -> TokenEnum {
    match tok {
        "module" => MODULE,
        "class" => CLASS,
        "instance" => INSTANCE,
        "where" => WHERE,
        "let" => LET,
        "in" => IN,
        "case" => CASE,
        "of" => OF,
        "->" => ARROW,
        "data" => DATA,
        "newtype" => NEWTYPE,
        "do" => DO,
        "import" => IMPORT,
        "infixl" => INFIXL,
        "infixr" => INFIXR,
        "infix" => INFIX,
        "deriving" => DERIVING,
        "if" => IF,
        "then" => THEN,
        "else" => ELSE,
        _ => NAME
    }
}
///Returns whether the character is a haskell operator
fn is_operator(first_char : char) -> bool {
    match first_char {
        '+' | '-' | '*' | '/' | '.' | '$' |
        ':' | '=' | '<' | '>' | '|' | '&' | '!' => true,
        _ => false
    }
}

pub struct Lexer<Stream: Iterator<Item=char>> {
    ///The input which the lexer processes
    input : Peekable<char, Stream>,
    ///The current location of the lexer
    location : Location,
    ///All the current unprocessed tokens stored on a stack
    unprocessedTokens : Vec<Token>,
    ///The token buffer which contains the last n produced tokens.
    tokens : RingBuf<Token>,
    ///A stack which contains the indentation levels of automatically inserted '{'
    indentLevels : Vec<int>,
    ///The offset into the token buffer at which the current token is at
    offset : uint,
    ///The string interner, cached here for efficency
    interner: Rc<RefCell<Interner>>
}


impl <Stream : Iterator<Item=char>> Lexer<Stream> {
    
    ///Constructs a new lexer with a default sized token buffer and the local string interner
    pub fn new(input : Stream) -> Lexer<Stream> {
        let start = Location { column : 0, row : 0, absolute : 0};
        Lexer { 
            input : input.peekable(),
            location : start,
            unprocessedTokens : Vec::new(),
            tokens : RingBuf::with_capacity(20),
            indentLevels : Vec::new(),
            offset : 0,
            interner: get_local_interner()
        }
    }
    ///Returns a new token with some special rules necessary for the parsing of the module declaration
    ///TODO check if this can be removed somehow
    pub fn module_next<'a>(&'a mut self) -> &'a Token {
        let mut newline = false;
        let n = self.next_indent_token(&mut newline);
        self.unprocessedTokens.push(n);
        let newTok = self.unprocessedTokens.get(self.unprocessedTokens.len() - 1).token;
        let loc = self.unprocessedTokens.get(self.unprocessedTokens.len() - 1).location;

        if newTok != LBRACE && newTok != MODULE {
            self.unprocessedTokens.push(Token::new(&self.interner, INDENTSTART, "{n}", loc));
        }
        if newline {
            self.unprocessedTokens.push(Token::new(&self.interner, INDENTLEVEL, "<n>", loc));
        }
        
        self.layout_independent_token();
        self.current()
    }

    pub fn peek<'a>(&'a mut self) -> &'a Token {
        if self.offset == 0 {
            self.next();
            self.backtrack();
        }
        self.tokens.iter()
            .idx(self.tokens.len() - self.offset)
            .unwrap()
    }
    
    ///Returns the next token in the lexer
    pub fn next<'a>(&'a mut self) -> &'a Token {
        if self.offset > 0 {
            //backtrack has been used so simply return the next token from the buffer
            self.offset -= 1;
            match self.tokens.iter().idx(self.tokens.len() - 1 - self.offset) {
                Some(token) => token,
                None => panic!("Impossible empty tokens stream")
            }
        }
        else if self.unprocessedTokens.len() > 0 {
            //Some previous call to next produced more than one token so process those first
            self.layout_independent_token();
            self.tokens.back().unwrap()
        }
        else {
            self.next_token()
        }
    }

    ///Returns a reference to the current token
    pub fn current<'a>(&'a self) -> &'a Token {
        match self.tokens.iter().idx(self.tokens.len() - 1 - self.offset) {
            Some(token) => token,
            None => panic!("Attempted to access Lexer::current() on when tokens is empty")
        }
    }

    ///Moves the lexer back one token
    ///TODO check for overflow in the buffer
    pub fn backtrack(&mut self) {
        self.offset += 1;
    }

    ///Returns true if the lexer is still valid (it has not hit EOF)
    pub fn valid(&self) -> bool {
        self.offset > 0 || match self.tokens.back() { None => true, Some(x) => x.token != EOF }
    }

    ///Peeks at the next character in the input
    fn peek_char(&mut self) -> Option<char> {
        self.input.peek().map(|c| *c)
    }

    ///Reads a character from the input and increments the current position
    fn read_char(&mut self) -> Option<char> {
        match self.input.next() {
            Some(c) => {
                self.location.absolute += 1;
                self.location.column += 1;
                if c == '\n' || c == '\r' {
                    self.location.column = 0;
                    self.location.row += 1;
                    //If this is a \n\r line ending skip the next char without increasing the location
                    let x = '\n';
                    if c == '\r' && self.input.peek() == Some(&x) {
                        self.input.next();
                    }
                }
                Some(c)
            }
            None => None
        }
    }

    ///Scans digits into a string
    fn scan_digits(&mut self) -> String {
        let mut result = String::new();
        loop {
            match self.peek_char() {
                Some(x) => {
                    if !x.is_digit() {
                        break;
                    }
                    self.read_char();
                    result.push_char(x)
                }
                None => break
            }
        }
        result
    }
    ///Scans a number, float or integer and returns the appropriate token
    fn scan_number(&mut self, c : char, location : Location) -> Token {
        let mut number = c.to_string();
        number.push_str(self.scan_digits().as_slice());
        let mut token = NUMBER;
        match self.peek_char() {
            Some('.') => {
                self.input.next();
                token = FLOAT;
                number.push_char('.');
                number.push_str(self.scan_digits().as_slice());
            }
            _ => ()
        }
        Token::new(&self.interner, token, number.as_slice(), location)
    }
    ///Scans an identifier or a keyword
    fn scan_identifier(&mut self, c: char, startLocation: Location) -> Token {
        let mut result = c.to_string();
        loop {
            match self.peek_char() {
                Some(ch) => {
                    if !ch.is_alphanumeric() && ch != '_' {
                        break;
                    }
                    self.read_char();
                    result.push_char(ch);
                }
                None => break
            }
        }
        return Token::new(&self.interner, name_or_keyword(result.as_slice()), result.as_slice(), startLocation);
    }

    ///Returns the next token but if it is not an '}' it will attempt to insert a '}' automatically
    pub fn next_end<'a>(&'a mut self) -> &'a Token {
        //If the next token is not an '}' and the starting '{' is not explicit we insert an '}'
        //before the current token and set the current token to the '}'
        //Credits to the HUGS source code for the solution
        if self.next().token != RBRACE {
            if self.indentLevels.len() != 0 {
                //L (t:ts) (m:ms) 	= 	} : (L (t:ts) ms) 	if m /= 0 and parse-error(t)
                let m = *self.indentLevels.get(self.indentLevels.len() - 1);
                if m != 0 {//If not a explicit '}'
                    debug!("ParseError on token {}, inserting }}", self.current().token);
                    self.indentLevels.pop();
                    let loc = self.current().location;
                    self.tokens.push_back(Token::new(&self.interner, RBRACE, "}", loc));
                    let len = self.tokens.len();
                    self.tokens.swap(len - 2, len - 1);
                    self.backtrack();
                }
            }
        }
        self.current()
    }
    
    ///Scans and returns the next token from the input stream, taking into account the indentation rules
    fn next_token<'a>(&'a mut self) -> &'a Token {
        let mut newline = false;
        let n = self.next_indent_token(&mut newline);
        self.unprocessedTokens.push(n);
        let newTok = self.unprocessedTokens.get(self.unprocessedTokens.len() - 1).token;

        if newTok != LBRACE {
            match self.tokens.back() {
                Some(tok) => {
                    if tok.token == LET || tok.token == WHERE || tok.token == OF || tok.token == DO {
                        let loc = self.unprocessedTokens.get(self.unprocessedTokens.len() - 1).location;
                        let indentstart = Token::new(&self.interner, INDENTSTART, "{n}", loc);
                        self.unprocessedTokens.push(indentstart);
                    }
                }
                None => ()
            }
        }
        if newline {
            let loc = self.unprocessedTokens.get(self.unprocessedTokens.len() - 1).location;
            self.unprocessedTokens.push(Token::new(&self.interner, INDENTLEVEL, "<n>", loc));
        }
        self.layout_independent_token();
        self.tokens.back().unwrap()
    }

    ///Looks at the next unprocessed token and applies the indentation rules on it
    ///and returns a token which is not affected by indentation
    fn layout_independent_token(&mut self) {
        if self.unprocessedTokens.len() > 0 {
            let tok = self.unprocessedTokens.get(self.unprocessedTokens.len() - 1).clone();//TODO dont use clone
            match tok.token {
                INDENTLEVEL => {
                    if self.indentLevels.len() > 0 {
                        //m:ms
                        let m = *self.indentLevels.get(self.indentLevels.len() - 1);
                        //m == n
                        if m == tok.location.column {
                            debug!("Indents are same, inserted semicolon");
                            self.tokens.push_back(Token::new(&self.interner, SEMICOLON, ";", tok.location));
                            self.unprocessedTokens.pop();
                            return;
                        }
                        else if tok.location.column < m {
                            //n < m
                            //TODO
                            debug!("n < m, insert }}");
                            self.indentLevels.pop();
                            self.tokens.push_back(Token::new(&self.interner, RBRACE, "}", tok.location));
                            return;
                        }
                    }
                    self.unprocessedTokens.pop();
                    if self.unprocessedTokens.len() == 0 {
                        self.next_token();
                        return;
                    }
                    else {
                        return self.layout_independent_token();
                    }
                }
                INDENTSTART => {
                    //{n} token
                    let n = tok.location.column;
                    if self.indentLevels.len() != 0 {
                        //m:ms
                        let m = *self.indentLevels.get(self.indentLevels.len() - 1);
                        if n > m {
                            debug!("n > m + INDENTSTART, insert {{");
                            self.unprocessedTokens.pop();
                            self.tokens.push_back(Token::new(&self.interner, LBRACE, "{", tok.location));
                            self.indentLevels.push(n);
                            return;
                        }
                    }
                    if n > 0 {
                        self.tokens.push_back(Token::new(&self.interner, LBRACE, "{", tok.location));
                        self.unprocessedTokens.pop();
                        self.indentLevels.push(n);
                        return;
                    }
                    self.tokens.push_back(Token::new(&self.interner, LBRACE, "{", tok.location));
                    self.tokens.push_back(Token::new(&self.interner, RBRACE, "}", tok.location));
                    self.unprocessedTokens.pop();
                    self.unprocessedTokens.push(Token::new(&self.interner, INDENTLEVEL, "<n>", tok.location));
                    self.offset += 1;
                    return;
                }
                RBRACE => {
                    if self.indentLevels.len() > 0 && *self.indentLevels.get(self.indentLevels.len() - 1) == 0 {
                        self.tokens.push_back(self.unprocessedTokens.pop().unwrap());
                        self.indentLevels.pop();
                        return;
                    }
                    else {
                        return;//parse-error
                    }
                }
                LBRACE => {
                    self.tokens.push_back(self.unprocessedTokens.pop().unwrap());
                    self.indentLevels.push(0);
                    return;
                }

                _ => ()
            }
            self.tokens.push_back(self.unprocessedTokens.pop().unwrap());
            return;
        }
        else {
            if self.indentLevels.len() == 0 {
                //End of stream
                return;
            }
            else if *self.indentLevels.get(self.indentLevels.len() - 1) != 0 {
                //Keep pusing right brackets
                self.indentLevels.pop();
                self.tokens.push_back(Token::new(&self.interner, RBRACE, "}", self.location));
                return;
            }
        }
    }
    
    ///Scans the character stream for the next token
    ///Return EOF token if the token stream has ehas ended
    fn next_indent_token(&mut self, newline : &mut bool) -> Token {
        let mut c = ' ';
        //Skip all whitespace before the token
        while c.is_whitespace() {
            match self.read_char() {
                Some(x) => {
                    c = x;
                    if self.location.column == 0 {//newline detected
                        *newline = true;
                    }
                }
                None => { return Token::eof() }
            }
        }
        let startLocation = self.location;

        //Decide how to tokenize depending on what the first char is
        //ie if its an operator then more operators will follow
        if is_operator(c) {
            let mut result = c.to_string();
            loop {
                match self.peek_char() {
                    Some(ch) => {
                        if !is_operator(ch) {
                            break;
                        }
                        self.read_char();
                        result.push_char(ch);
                    }
                    None => { break; }
                }
            }
            let tok = match result.as_slice() {
                "="  => EQUALSSIGN,
                "->" => ARROW,
                "<-" => LARROW,
                "::" => TYPEDECL,
                "=>" => CONTEXTARROW,
                "|"  => PIPE,
                _    => OPERATOR
            };
            return Token::new(&self.interner, tok, result.as_slice(), startLocation);
        }
        else if c.is_digit() {
            return self.scan_number(c, startLocation);
        }
        else if c.is_alphabetic() || c == '_' {
            return self.scan_identifier(c, startLocation);
        }
        else if c == '`' {
            let x = self.read_char().expect("Unexpected end of input");
            if !x.is_alphabetic() && x != '_' {
                panic!("Parse error on '{}'", x);
            }
            let mut token = self.scan_identifier(x, startLocation);
            let end_tick = self.read_char();
            match end_tick {
                Some('`') => (),
                Some(x) => panic!("Parse error on '{}'", x),
                None => panic!("Unexpected end of input")
            }
            token.token = OPERATOR;
            return token;
        }
        else if c == '"' {
            let mut string = String::new();
            loop {
                match self.read_char() {
                    Some('"') => return Token::new(&self.interner, STRING, string.as_slice(), startLocation),
                    Some(x) => string.push_char(x),
                    None => panic!("Unexpected EOF")
                }
            }
        }
        else if c == '\'' {
            match self.read_char() {
                Some(x) => {
                    if self.read_char() == Some('\'') {
                        //FIXME: Slow
                        return Token::new(&self.interner, CHAR, &*x.to_string(), startLocation);
                    }
                    else {
                        panic!("Multi char character")
                    }
                }
                None => panic!("Unexpected EOF")
            }
        }
        let tok = match c {
            ';' => SEMICOLON,
            '(' => LPARENS,
            ')' => RPARENS,
            '[' => LBRACKET,
            ']' => RBRACKET,
            '{' => LBRACE,
            '}' => RBRACE,
            ',' => COMMA,
            '\\'=> LAMBDA,
            _   => EOF
        };
        //FIXME: Slow
        Token::new(&self.interner, tok, c.to_string().as_slice(), startLocation)
    }
}

#[cfg(test)]
mod tests {

use lexer::*;

#[test]
fn simple() {
    let mut lexer = Lexer::new("test 2 + 3".chars());

    assert_eq!(*lexer.next(), Token::new_(NAME, "test"));
    assert_eq!(*lexer.next(), Token::new_(NUMBER, "2"));
    assert_eq!(*lexer.next(), Token::new_(OPERATOR, "+"));
    assert_eq!(*lexer.next(), Token::new_(NUMBER, "3"));
}
#[test]
fn let_bind() {
    let mut lexer = Lexer::new(
r"let
    test = 2 + 3
in test".chars());

    assert_eq!(*lexer.next(), Token::new_(LET, "let"));
    assert_eq!(*lexer.next(), Token::new_(LBRACE, "{"));
    assert_eq!(*lexer.next(), Token::new_(NAME, "test"));
    assert_eq!(*lexer.next(), Token::new_(EQUALSSIGN, "="));
    assert_eq!(*lexer.next(), Token::new_(NUMBER, "2"));
    assert_eq!(*lexer.next(), Token::new_(OPERATOR, "+"));
    assert_eq!(*lexer.next(), Token::new_(NUMBER, "3"));
}

}
