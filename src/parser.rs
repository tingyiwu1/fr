use std::iter::Peekable;

use crate::{
    lexer::{self, Lexer, Token},
    utils::{Copyable, Expr, Lifetime, Lval, Mutable, Stmt},
};

pub struct Parser<'a> {
    lexer: Peekable<Lexer<'a>>,
    fresh_lifetime: Lifetime,
}
#[derive(Debug)]
pub enum Error {
    EndOfFile,
    Lexer(lexer::Error),
    Unexpected(lexer::Token),
}

type ParseResult<T> = Result<T, Error>;

impl<'a> Parser<'a> {
    pub fn new(contents: &'a str) -> Self {
        Parser {
            lexer: Lexer::new(contents).peekable(),
            fresh_lifetime: Lifetime(0),
        }
    }

    fn fresh_lifetime(&mut self) -> Lifetime {
        self.fresh_lifetime.0 += 1;
        self.fresh_lifetime
    }

    fn next_token(&mut self) -> ParseResult<Token> {
        match self.lexer.next() {
            Some(Ok(token)) => Ok(token),
            Some(Err(err)) => Err(Error::Lexer(err)),
            None => Err(Error::EndOfFile),
        }
    }

    fn next_token_match(&mut self, t: Token) -> ParseResult<Token> {
        let token = self.next_token()?;
        if token != t {
            Err(Error::Unexpected(token))
        } else {
            Ok(token)
        }
    }

    fn next_token_var(&mut self) -> ParseResult<String> {
        let token = self.next_token()?;
        match token {
            Token::Var(ident) => Ok(ident.clone()),
            _ => Err(Error::Unexpected(token)),
        }
    }

    fn peek_token(&mut self) -> Result<&Token, Error> {
        let token = self.lexer.peek();
        match token {
            Some(Ok(token)) => Ok(token),
            _ => Err(Error::EndOfFile),
        }
    }

    fn parse_let_mut(&mut self) -> ParseResult<Stmt> {
        self.next_token_match(Token::Let)?;
        self.next_token_match(Token::Mut)?;
        let x = self.next_token_var()?;
        self.next_token_match(Token::Eq)?;
        let expr = self.parse_expr()?;
        Ok(Stmt::LetMut(x, expr))
    }

    fn parse_lval(&mut self) -> ParseResult<Lval> {
        // println!("parsing lval");
        // dbg!(self.peek_token()?);
        let mut derefs = 0;
        loop {
            match self.next_token()? {
                Token::Star => derefs += 1,
                Token::Var(ident) => {
                    // dbg!(&ident);
                    return Ok(Lval::deref(derefs, &ident));
                }
                t => return Err(Error::Unexpected(t)),
            }
        }
    }

    fn parse_borrow(&mut self) -> ParseResult<Expr> {
        self.next_token_match(Token::Ampersand)?;
        let mut mutable = Mutable::No;
        if let Token::Mut = self.peek_token()? {
            self.next_token_match(Token::Mut)?;
            mutable = Mutable::Yes;
        }
        Ok(Expr::Borrow(self.parse_lval()?, mutable))
    }

    fn parse_box(&mut self) -> ParseResult<Expr> {
        self.next_token_match(Token::Box)?;
        self.next_token_match(Token::Lparen)?;
        let e = self.parse_expr()?;
        self.next_token_match(Token::Rparen)?;
        Ok(Expr::Box(Box::new(e)))
    }

    fn parse_assert_eq(&mut self) -> ParseResult<Expr> {
        self.next_token_match(Token::AssertEq)?;
        self.next_token_match(Token::Lparen)?;
        let e1 = self.parse_expr()?;
        self.next_token_match(Token::Comma)?;
        let e2 = self.parse_expr()?;
        self.next_token_match(Token::Rparen)?;
        Ok(Expr::assert_eq(e1, e2))
    }

    fn parse_if_else(&mut self) -> ParseResult<Expr> {
        self.next_token_match(Token::If)?;
        let cond = self.parse_expr()?;
        let b1 = self.parse_block()?;
        self.next_token_match(Token::Else)?;
        let b2 = self.parse_block()?;

        let (Expr::Block(s1, e1, l1), Expr::Block(s2, e2, l2)) = (b1, b2) else {
            panic!();
        };
        Ok(Expr::if_else(cond, (s1, *e1, l1), (s2, *e2, l2)))
    }

    fn parse_block(&mut self) -> ParseResult<Expr> {
        self.next_token_match(Token::Lbracket)?;
        let mut stmts = vec![];
        let mut ret = Expr::Unit;
        loop {
            let stmt = match self.peek_token()? {
                Token::Rbracket => Stmt::Expr(Expr::Unit),
                Token::Let => self.parse_let_mut()?,
                _ => {
                    let expr = self.parse_expr()?;
                    match self.peek_token()? {
                        Token::Eq => {
                            let Expr::Lval(lval, ..) = expr else {
                                return Err(Error::Unexpected(Token::Eq));
                            };
                            self.next_token_match(Token::Eq)?;
                            let expr2 = self.parse_expr()?;
                            Stmt::Assign(lval, expr2)
                        }
                        _ => Stmt::Expr(expr),
                    }
                }
            };
            // handles some cases in rust but not in grammar
            match (stmt, self.peek_token()?) {
                // any statement with ; goes in stmts
                (stmt, Token::Semicolon) => {
                    self.next_token_match(Token::Semicolon)?;
                    stmts.push(stmt);
                }
                // let mut always requires ; even at end of block
                (Stmt::LetMut(..), Token::Rbracket) => {
                    return Err(Error::Unexpected(self.next_token()?));
                }
                // expression at end of block returns e
                (Stmt::Expr(e), Token::Rbracket) => {
                    self.next_token_match(Token::Rbracket)?;
                    ret = e;
                    break;
                }
                // statement at end of block goes in stmts and returns Unit
                (stmt, Token::Rbracket) => {
                    self.next_token_match(Token::Rbracket)?;
                    stmts.push(stmt);
                    break;
                }
                // blocks don't need ; as a standalone stmt, returning block covered in expr case
                (block @ Stmt::Expr(Expr::Block(..)), _) => {
                    stmts.push(block);
                }
                _ => return Err(Error::Unexpected(self.next_token()?)),
            }
        }
        Ok(Expr::Block(stmts, Box::new(ret), self.fresh_lifetime()))
    }

    fn parse_expr(&mut self) -> ParseResult<Expr> {
        let e = self.parse_expr1()?;

        if let Token::Equals = self.peek_token()? {
            self.next_token_match(Token::Equals)?;
            let e2 = self.parse_expr1()?;
            return Ok(Expr::equals(e, e2));
        }
        Ok(e)
    }

    fn parse_expr1(&mut self) -> ParseResult<Expr> {
        let e = match self.peek_token()? {
            Token::Lparen => {
                self.next_token_match(Token::Lparen)?;
                match self.peek_token()? {
                    Token::Rparen => {
                        self.next_token_match(Token::Rparen)?;
                        Expr::Unit
                    }
                    _ => {
                        let e = self.parse_expr()?;
                        self.next_token_match(Token::Rparen)?;
                        e
                    }
                }
            }
            Token::Int(_) => {
                let Token::Int(i) = self.next_token()? else {
                    panic!();
                };
                Expr::Int(i)
            }
            Token::True => {
                self.next_token_match(Token::True)?;
                Expr::Bool(true)
            }
            Token::False => {
                self.next_token_match(Token::False)?;
                Expr::Bool(false)
            }
            Token::Star | Token::Var(_) => Expr::Lval(self.parse_lval()?, Copyable::No),
            Token::Box => self.parse_box()?,
            Token::AssertEq => self.parse_assert_eq()?,
            Token::If => self.parse_if_else()?,
            Token::Ampersand => self.parse_borrow()?,
            Token::Lbracket => self.parse_block()?,
            _ => return Err(Error::Unexpected(self.next_token()?)),
        };
        Ok(e)
    }

    pub fn parse(&mut self) -> ParseResult<Expr> {
        self.next_token_match(Token::Fn)?;
        let main = self.next_token()?;
        match main {
            Token::Var(ident) if ident == "main" => {
                self.next_token_match(Token::Lparen)?;
                self.next_token_match(Token::Rparen)?;
                let out = self.parse_block()?;
                if self.peek_token().is_err() {
                    return Ok(out);
                }
                Err(Error::Unexpected(self.next_token()?))
            }
            _ => Err(Error::Unexpected(main)),
        }
    }
}
