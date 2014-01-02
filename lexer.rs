use std::iter::Peekable;
#[deriving(Eq, ToStr)]
enum TokenEnum {
	EOF,
	NAME,
	OPERATOR,
	NUMBER,
	FLOAT,
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
	TYPEDECL,
	DATA
}

#[deriving(Eq, ToStr)]
struct Location {
    column : int,
    row : int,
    absolute : int
}

struct Token {
    token : TokenEnum,
    value : ~str,
    location : Location
}
impl Token {
    fn eof() -> Token {
        Token { token : EOF, value : ~"", location : Location { column : -1, row : -1, absolute : -1} }
    }

    fn new(token : TokenEnum, value : ~str) -> Token {
        Token { token : token, value : value, location : Location { column : -1, row : -1, absolute : -1 } }
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
        _ => NAME
    }
}

fn is_operator(first_char : char) -> bool {
    match first_char {
        '+' => true,
        '-' => true,
        '*' => true,
        '/' => true,
        '.' => true,
        '$' => true,
        ':' => true,
        '=' => true,
        '<' => true,
        '>' => true,
        '|' => true,
        '&' => true,
        _ => false
    }
}

struct Lexer<Stream> {
    input : Peekable<char, Stream>,
    location : Location,
    previousLocation : Location
}


impl <Stream : Iterator<char>> Lexer<Stream> {
    
    pub fn new(input : Stream) -> Lexer<Stream> {
        let start = Location { column : 0, row : 0, absolute : 0};
        Lexer { input : input.peekable(), location : start, previousLocation : start }
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
                self.location = self.location;
                self.location.absolute += 1;
                self.location.column += 1;
                if (c == '\n' || c == '\r')
                {
                    self.location.column = 0;
                    self.location.row += 1;
                }
                Some(c)
            }
            None => None
        }
    }

    fn scan_digits(&mut self) -> ~str {
        let mut result = ~"";
        loop {
            match self.peek() {
                Some(x) => {
                    if !x.is_digit() {
                        return result;
                    }
                    self.read_char();
                    result.push_char(x)
                }
                None => return result
            }
        }
        result
    }

    fn scan_number(&mut self, c : char) -> Token {
        let mut number = c.to_str() + self.scan_digits();
        let mut token = NUMBER;
        match self.peek() {
            Some('.') => {
                token = FLOAT;
                number.push_char('.');
                number = number.append(self.scan_digits());
            }
            _ => ()
        }
        Token { token : NUMBER, value : number, location : self.location }
    }

    pub fn next(&mut self) -> Token {
        let mut c = ' ';
        //Skip all whitespace before the token
        while c.is_whitespace() {
            match self.read_char() {
                Some(x) => {
                    c = x;
                    if (self.location.column == 0)//newline detected
                    {
                        //*newline = true;
                    }
                }
                None => { return Token::eof() }
            }
        }

        //Decide how to tokenize depending on what the first char is
        //ie if its an operator then more operators will follow
        if (is_operator(c))
        {
            let mut result = c.to_str();
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
            let tok = match result {
                ~"="  => EQUALSSIGN,
                ~"->" => ARROW,
                ~"::" => TYPEDECL,
                _    => OPERATOR
            };
            return Token { token : tok, value : result, location : self.location };
        }
        else if (c.is_digit())
        {
            return self.scan_number(c);
        }
        else if (c.is_alphabetic() || c == '_')
        {
            let mut result = c.to_str();
            loop {
                match self.peek() {
                    Some(ch) => {
                        if !ch.is_alphanumeric() && ch != '_' {
                            break;
                        }
                        self.read_char();
                        result.push_char(ch);
                    }
                    None => return Token::eof()
                }
            }
            return Token {
                token : name_or_keyword(result),
                location : self.location,
                value : result};
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
            _   => EOF
        };
        Token { token : tok, location : self.location, value : c.to_str() }
    }
}


#[test]
fn test() {
    let mut lexer = Lexer::new("test 2 + 3".chars());

    assert_eq!(lexer.next(), Token::new(NAME, ~"test"));
    assert_eq!(lexer.next(), Token::new(NUMBER, ~"2"));
    assert_eq!(lexer.next(), Token::new(OPERATOR, ~"+"));
    assert_eq!(lexer.next(), Token::new(NUMBER, ~"3"));
}
