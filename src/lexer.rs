use std::str::Lines;

#[derive(Debug, PartialEq)]
pub enum Token {
    Lparen,
    Rparen,
    Lbracket,
    Rbracket,
    Eq,
    Equals,
    Ampersand,
    Star,
    Comma,
    Semicolon,
    Fn,
    Let,
    Mut,
    Box,
    AssertEq,
    If,
    Else,
    True,
    False,
    Int(i32),
    Var(String),
}

impl Token {
    fn is_variable_char(c: char) -> bool {
        c.is_ascii_lowercase() || c == '_'
    }
}

const LEXEMES: [(&str, Token); 19] = [
    ("(", Token::Lparen),
    (")", Token::Rparen),
    ("{", Token::Lbracket),
    ("}", Token::Rbracket),
    ("==", Token::Equals),
    ("=", Token::Eq),
    ("&", Token::Ampersand),
    ("*", Token::Star),
    (",", Token::Comma),
    (";", Token::Semicolon),
    ("fn", Token::Fn),
    ("let", Token::Let),
    ("mut", Token::Mut),
    ("assert_eq!", Token::AssertEq),
    ("if", Token::If),
    ("else", Token::Else),
    ("true", Token::True),
    ("false", Token::False),
    ("Box::new", Token::Box),
];

pub struct Lexer<'a> {
    contents: Lines<'a>,
    pub curr_line_num: usize,
    pub curr_col_num: usize,
    curr_line: &'a str,
}

#[derive(Debug)]
pub enum Error {
    Unknown(usize, usize),
}

type LexResult = Result<Token, Error>;

impl<'a> Lexer<'a> {
    pub fn new(contents: &'a str) -> Self {
        let mut lexer = Lexer {
            contents: contents.lines(),
            curr_line_num: 0,
            curr_col_num: 0,
            curr_line: "",
        };
        lexer.trim_start();
        lexer
    }

    fn done(&self) -> bool {
        self.curr_line.is_empty()
    }

    fn trim_start(&mut self) {
        let before = self.curr_line.len();
        self.curr_line = self.curr_line.trim_start();
        self.curr_col_num += before - self.curr_line.len();
        while self.curr_line.is_empty() || self.curr_line.starts_with("//") {
            match self.contents.next() {
                Some(line) => {
                    self.curr_line_num += 1;
                    self.curr_line = line.trim_start();
                    self.curr_col_num = line.len() - self.curr_line.len();
                }
                None => {
                    self.curr_line = "";
                    break;
                }
            }
        }
    }

    fn unknown(&self) -> Error {
        Error::Unknown(self.curr_line_num, self.curr_col_num)
    }

    // remove `i` characters and remove any leading whitespace from the
    // result (including empty lines)
    fn consume(&mut self, i: usize) {
        if i > self.curr_line.len() {
            self.curr_line = "";
            self.trim_start();
        }
        self.curr_line = &self.curr_line[i..];
        self.curr_col_num += i;
        self.trim_start();
    }

    fn symbol_or_keyword(&mut self) -> LexResult {
        for (lexeme, token) in LEXEMES {
            if self.curr_line.starts_with(lexeme) {
                self.consume(lexeme.len());
                return Ok(token);
            }
        }
        Err(self.unknown())
    }

    // similar to `symbol_or_keyword` but for variables
    fn variable(&mut self) -> LexResult {
        let len = self
            .curr_line
            .find(|c: char| !Token::is_variable_char(c))
            .unwrap_or(self.curr_line.len());
        if len > 0 {
            let t = Token::Var(String::from(&self.curr_line[..len]));
            self.consume(len);
            return Ok(t);
        }
        Err(self.unknown())
    }

    // similar to `symbol_or_keyword` for but integer literals
    fn int(&mut self) -> LexResult {
        let start = self.curr_line.starts_with("-") as usize;
        let len = start
            + self.curr_line[start..]
                .find(|c: char| !c.is_digit(10))
                .unwrap_or(self.curr_line.len());

        if len > start {
            let parsed: i32 = (&self.curr_line[..len]).parse().expect("should succeed");
            self.consume(len);
            return Ok(Token::Int(parsed));
        }
        Err(self.unknown())
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = LexResult;
    fn next(&mut self) -> Option<LexResult> {
        if self.done() {
            None
        } else {
            Some(
                self.symbol_or_keyword()
                    .or_else(|_| self.variable())
                    .or_else(|_| self.int()),
            )
        }
    }
}
