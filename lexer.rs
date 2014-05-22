use std::fmt;
use collections::{Deque, RingBuf};
use std::iter::Peekable;
#[deriving(Clone, Eq, Show)]
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
    LAMBDA,
    DO
}

#[deriving(Clone, Eq)]
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

impl <T: Eq> Eq for Located<T> {
    fn eq(&self, o: &Located<T>) -> bool {
        self.node == o.node
    }
}
    

impl fmt::Show for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f.buf, "{}:{}", self.row, self.column)
    }
}

#[deriving(Clone, Show)]
pub struct Token {
    pub token : TokenEnum,
    pub value : ~str,
    pub location : Location
}
impl Token {
    fn eof() -> Token {
        Token { token : EOF, value : ~"", location : Location { column : -1, row : -1, absolute : -1} }
    }

    fn new(token : TokenEnum, value : ~str, loc : Location) -> Token {
        Token { token : token, value : value, location : loc }
    }
    #[cfg(test)]
    fn new_(token : TokenEnum, value : ~str) -> Token {
        Token::new(token, value, Location { column : -1, row : -1, absolute : -1 })
    }
}

impl Eq for Token {
    fn eq(&self, rhs : &Token) -> bool {
        self.token == rhs.token && self.value == rhs.value
    }
}

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
        "do" => DO,
        _ => NAME
    }
}

fn is_operator(first_char : char) -> bool {
    match first_char {
        '+' | '-' | '*' | '/' | '.' | '$' |
        ':' | '=' | '<' | '>' | '|' | '&' | '!' => true,
        _ => false
    }
}

pub struct Lexer<Stream> {
    input : Peekable<char, Stream>,
    location : Location,
    previousLocation : Location,
    unprocessedTokens : Vec<Token>,
    tokens : RingBuf<Token>,
    indentLevels : Vec<int>,
    offset : uint
}


impl <Stream : Iterator<char>> Lexer<Stream> {
    
    pub fn new(input : Stream) -> Lexer<Stream> {
        let start = Location { column : 0, row : 0, absolute : 0};
        Lexer { 
            input : input.peekable(),
            location : start,
            previousLocation : start,
            unprocessedTokens : Vec::new(),
            tokens : RingBuf::with_capacity(20),
            indentLevels : Vec::new(),
            offset : 0}
    }
    pub fn module_next<'a>(&'a mut self) -> &'a Token {
        let mut newline = false;
        let n = self.next_indent_token(&mut newline);
        self.unprocessedTokens.push(n);
        let newTok = self.unprocessedTokens.get(self.unprocessedTokens.len() - 1).token;
        let loc = self.unprocessedTokens.get(self.unprocessedTokens.len() - 1).location;

        if newTok != LBRACE && newTok != MODULE {
            self.unprocessedTokens.push(Token::new(INDENTSTART, ~"{n}", loc));
        }
        if newline {
            self.unprocessedTokens.push(Token::new(INDENTLEVEL, ~"<n>", loc));
        }
        
        self.layout_independent_token(|_| false);
        self.current()
    }

    pub fn next_<'a>(&'a mut self) -> &'a Token {
        self.next(|_| false)
    }
    pub fn next<'a>(&'a mut self, parseError : |&Token| -> bool) -> &'a Token {
        if self.offset > 0 {
            self.offset -= 1;
            match self.tokens.iter().idx(self.tokens.len() - 1 - self.offset) {
                Some(token) => token,
                None => fail!("Impossible empty tokens stream")
            }
        }
        else if self.unprocessedTokens.len() > 0 {
            self.layout_independent_token(parseError);
            self.tokens.back().unwrap()
        }
        else {
            self.new_token(parseError)
        }
    }

    pub fn current<'a>(&'a self) -> &'a Token {
        match self.tokens.iter().idx(self.tokens.len() - 1 - self.offset) {
            Some(token) => token,
            None => fail!("Attempted to access Lexer::current() on when tokens is empty")
        }
    }

    pub fn backtrack(&mut self) {
        self.offset += 1;
    }

    pub fn valid(&self) -> bool {
        self.offset > 0 || match self.tokens.back() { None => true, Some(x) => x.token != EOF }
    }

    fn peek(&mut self) -> Option<char> {
        match self.input.peek() {
            Some(ch) => Some(*ch),
            None => None
        }
    }

    fn read_char(&mut self) -> Option<char> {
        match self.input.next() {
            Some(c) => {
                self.previousLocation = self.location;
                self.location.absolute += 1;
                self.location.column += 1;
                if (c == '\n' || c == '\r')
                {
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

    fn scan_digits(&mut self) -> ~str {
        let mut result = StrBuf::new();
        loop {
            match self.peek() {
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
        result.into_owned()
    }

    fn scan_number(&mut self, c : char, location : Location) -> Token {
        let mut number = StrBuf::from_char(1, c);
        number.push_str(self.scan_digits());
        let mut token = NUMBER;
        match self.peek() {
            Some('.') => {
                self.input.next();
                token = FLOAT;
                number.push_char('.');
                number.push_str(self.scan_digits());
            }
            _ => ()
        }
        Token { token : token, value : number.into_owned(), location : location }
    }

    fn scan_identifier(&mut self, c: char, startLocation: Location) -> Token {
        let mut result = StrBuf::from_char(1, c);
        loop {
            match self.peek() {
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
        return Token {
            token : name_or_keyword(result.as_slice()),
            location : startLocation,
            value : result.into_owned()};
    }
 
    fn new_token<'a>(&'a mut self, parseError : |&Token| -> bool) -> &'a Token {
        let mut newline = false;
        let n = self.next_indent_token(&mut newline);
        self.unprocessedTokens.push(n);
        let newTok = self.unprocessedTokens.get(self.unprocessedTokens.len() - 1).token;

        if newTok != LBRACE {
            match self.tokens.back() {
                Some(tok) => {
                    if tok.token == LET || tok.token == WHERE || tok.token == OF || tok.token == DO {
                        let loc = self.unprocessedTokens.get(self.unprocessedTokens.len() - 1).location;
                        let indentstart = Token { token : INDENTSTART, value : ~"{n}", location : loc };
                        self.unprocessedTokens.push(indentstart);
                    }
                }
                None => ()
            }
        }
        if newline {
            let loc = self.unprocessedTokens.get(self.unprocessedTokens.len() - 1).location;
            self.unprocessedTokens.push(Token::new(INDENTLEVEL, ~"<n>", loc));
        }
        self.layout_independent_token(parseError);
        self.tokens.back().unwrap()
    }

    fn layout_independent_token(&mut self, parseError : |&Token| -> bool) {
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
                            self.tokens.push_back(Token::new(SEMICOLON, ~";", tok.location));
                            self.unprocessedTokens.pop();
                            return;
                        }
                        else if tok.location.column < m {
                            //n < m
                            //TODO
                            debug!("n < m, insert \\}");
                            self.indentLevels.pop();
                            self.tokens.push_back(Token::new(RBRACE, ~"}", tok.location));
                            return;
                        }
                    }
                    self.unprocessedTokens.pop();
                    if self.unprocessedTokens.len() == 0 {
                        self.new_token(parseError);
                        return;
                    }
                    else {
                        return self.layout_independent_token(parseError);
                    }
                }
                INDENTSTART => {
                    //{n} token
                    let n = tok.location.column;
                    if self.indentLevels.len() != 0 {
                        //m:ms
                        let m = *self.indentLevels.get(self.indentLevels.len() - 1);
                        if n > m {
                            debug!("n > m + INDENTSTART, insert \\{");
                            self.unprocessedTokens.pop();
                            self.tokens.push_back(Token::new(LBRACE, ~"{", tok.location));
                            self.indentLevels.push(n);
                            return;
                        }
                    }
                    if n > 0 {
                        self.tokens.push_back(Token::new(LBRACE, ~"{", tok.location));
                        self.unprocessedTokens.pop();
                        self.indentLevels.push(n);
                        return;
                    }
                    self.tokens.push_back(Token::new(LBRACE, ~"{", tok.location));
                    self.tokens.push_back(Token::new(RBRACE, ~"}", tok.location));
                    self.unprocessedTokens.pop();
                    self.unprocessedTokens.push(Token::new(INDENTLEVEL, ~"<n>", tok.location));
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
            if self.indentLevels.len() != 0 {
                //L (t:ts) (m:ms) 	= 	} : (L (t:ts) ms) 	if m /= 0 and parse-error(t)
                let m = *self.indentLevels.get(self.indentLevels.len() - 1);
                if m != 0 && parseError(&tok) {
                    debug!("ParseError on token {:?}, inserting \\}", tok.token);
                    self.tokens.push_back(Token::new(RBRACE, ~"}", tok.location));
                    self.indentLevels.pop();
                    return;
                }
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
                self.tokens.push_back(Token::new(RBRACE, ~"}", self.location));
                return;
            }
        }
    }

    fn next_indent_token(&mut self, newline : &mut bool) -> Token {
        let mut c = ' ';
        //Skip all whitespace before the token
        while c.is_whitespace() {
            match self.read_char() {
                Some(x) => {
                    c = x;
                    if (self.location.column == 0)//newline detected
                    {
                        *newline = true;
                    }
                }
                None => { return Token::eof() }
            }
        }
        let startLocation = self.location;

        //Decide how to tokenize depending on what the first char is
        //ie if its an operator then more operators will follow
        if (is_operator(c))
        {
            let mut result = StrBuf::from_char(1, c);
            loop {
                match self.peek() {
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
                _    => OPERATOR
            };
            return Token { token : tok, value : result.into_owned(), location : startLocation };
        }
        else if (c.is_digit())
        {
            return self.scan_number(c, startLocation);
        }
        else if (c.is_alphabetic() || c == '_')
        {
            return self.scan_identifier(c, startLocation);
        }
        else if c == '`' {
            let x = self.read_char().expect("Unexpected end of input");
            if !x.is_alphabetic() && x != '_' {
                fail!("Parse error on '{}'", x);
            }
            let mut token = self.scan_identifier(x, startLocation);
            let end_tick = self.read_char();
            match end_tick {
                Some('`') => (),
                Some(x) => fail!("Parse error on '{}'", x),
                None => fail!("Unexpected end of input")
            }
            token.token = OPERATOR;
            return token;
        }
        else if c == '"' {
            let mut string = StrBuf::new();
            loop {
                match self.read_char() {
                    Some('"') => return Token { token: STRING, location: startLocation, value: string.into_owned() },
                    Some(x) => string.push_char(x),
                    None => fail!("Unexpected EOF")
                }
            }
        }
        else if c == '\'' {
            match self.read_char() {
                Some(x) => {
                    if self.read_char() == Some('\'') {
                        return Token { token:CHAR, location: startLocation, value: ::std::str::from_char(x) };
                    }
                    else {
                        fail!("Multi char character")
                    }
                }
                None => fail!("Unexpected EOF")
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
        Token { token : tok, location : startLocation, value : c.to_str() }
    }
}

#[cfg(test)]
mod tests {

use lexer::*;

#[test]
fn simple() {
    let mut lexer = Lexer::new("test 2 + 3".chars());

    assert_eq!(*lexer.next_(), Token::new_(NAME, ~"test"));
    assert_eq!(*lexer.next_(), Token::new_(NUMBER, ~"2"));
    assert_eq!(*lexer.next_(), Token::new_(OPERATOR, ~"+"));
    assert_eq!(*lexer.next_(), Token::new_(NUMBER, ~"3"));
}
#[test]
fn let_bind() {
    let mut lexer = Lexer::new(
r"let
    test = 2 + 3
in test".chars());

    assert_eq!(*lexer.next_(), Token::new_(LET, ~"let"));
    assert_eq!(*lexer.next_(), Token::new_(LBRACE, ~"{"));
    assert_eq!(*lexer.next_(), Token::new_(NAME, ~"test"));
    assert_eq!(*lexer.next_(), Token::new_(EQUALSSIGN, ~"="));
    assert_eq!(*lexer.next_(), Token::new_(NUMBER, ~"2"));
    assert_eq!(*lexer.next_(), Token::new_(OPERATOR, ~"+"));
    assert_eq!(*lexer.next_(), Token::new_(NUMBER, ~"3"));
}

}
