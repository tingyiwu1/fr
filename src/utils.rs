use std::fmt::Display;

pub type Ident = String;

#[derive(Debug, PartialEq, Clone)]
pub enum Copyable {
    Yes,
    No,
}
#[derive(Debug, PartialEq, Clone)]
pub enum Mutable {
    Yes,
    No,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Lifetime(pub usize);

impl Lifetime {
    pub fn global() -> Lifetime {
        Lifetime(0)
    }
}

impl Display for Lifetime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            if self.0 == usize::MAX {
                "*".to_owned()
            } else {
                format!("{}", self.0)
            }
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Lval {
    pub ident: Ident,
    pub derefs: usize,
}

impl Lval {
    pub fn var(ident: &str) -> Lval {
        Lval {
            ident: ident.to_owned(),
            derefs: 0,
        }
    }
    pub fn deref(derefs: usize, ident: &str) -> Lval {
        Lval {
            ident: ident.to_owned(),
            derefs,
        }
    }
    pub fn new(ident: &str, derefs: usize) -> Lval {
        Lval {
            ident: ident.to_owned(),
            derefs,
        }
    }
}

impl Display for Lval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", "*".repeat(self.derefs), self.ident)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Unit,
    Int(i32),
    Lval(Lval, Copyable),
    Box(Box<Expr>),
    Borrow(Lval, Mutable),
    AssertEq(Box<Expr>, Box<Expr>),
    Block(Vec<Stmt>, Box<Expr>, Lifetime),
}

impl Expr {
    pub fn boxx(expr: Expr) -> Expr {
        Expr::Box(Box::new(expr))
    }
    pub fn assert_eq(left: Expr, right: Expr) -> Expr {
        Expr::AssertEq(Box::new(left), Box::new(right))
    }
    pub fn block(stmts: Vec<Stmt>, l: Lifetime) -> Expr {
        Expr::Block(stmts, Box::new(Expr::Unit), l)
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Unit => write!(f, "ε"),
            Expr::Int(i) => write!(f, "{}", i),
            Expr::Lval(lval, copyable) => write!(
                f,
                "{}{}",
                lval,
                match copyable {
                    Copyable::Yes => "^",
                    Copyable::No => "",
                }
            ),
            Expr::Box(expr) => write!(f, "Box::new({})", *expr),
            Expr::Borrow(lval, mutable) => write!(
                f,
                "&{}{}",
                match mutable {
                    Mutable::Yes => "mut ",
                    Mutable::No => "",
                },
                lval
            ),
            Expr::AssertEq(e1, e2) => write!(f, "assert_eq!({}, {})", *e1, *e2),
            Expr::Block(_stmts, expr, lifetime) => {
                write!(f, "{{[..]; {}}} '{}", *expr, lifetime)
            }
        }
    }
}
#[derive(Debug, PartialEq, Clone)]
pub enum Stmt {
    Assign(Lval, Expr),
    LetMut(Ident, Expr),
    Expr(Expr),
}

impl Stmt {
    pub fn let_mut(ident: &str, expr: Expr) -> Stmt {
        Stmt::LetMut(ident.to_owned(), expr)
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Stmt::Assign(lval, expr) => write!(f, "{} = {}", lval, expr),
            Stmt::LetMut(x, expr) => write!(f, "let mut {} = {}", x, expr),
            Stmt::Expr(expr) => write!(f, "{}", expr),
        }
    }
}
