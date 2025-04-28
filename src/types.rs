use std::{collections::HashMap, fmt::Display, mem};

use crate::utils::{Copyable, Expr, Ident, Lifetime, Lval, Mutable, Stmt};

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    Unit,
    Int,
    Box(Box<Type>),
    Ref(Lval, Mutable),
    Undefined(Box<Type>),
}

impl Type {
    pub fn boxx(tipe: Type) -> Type {
        Type::Box(Box::new(tipe))
    }
    pub fn imm_ref(lval: Lval) -> Type {
        Type::Ref(lval, Mutable::No)
    }
    pub fn mut_ref(lval: Lval) -> Type {
        Type::Ref(lval, Mutable::Yes)
    }
    pub fn undefined(tipe: Type) -> Type {
        Type::Undefined(Box::new(tipe))
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Unit => write!(f, "ε"),
            Type::Int => write!(f, "int"),
            Type::Box(t) => write!(f, "□{}", t),
            Type::Ref(lval, Mutable::Yes) => write!(f, "&mut {}", lval),
            Type::Ref(lval, Mutable::No) => write!(f, "&{}", lval),
            Type::Undefined(t) => write!(f, "⌊{}⌋", t),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Slot {
    pub tipe: Type,
    lifetime: Lifetime,
}

impl Slot {
    pub fn new(tipe: Type, lifetime: Lifetime) -> Slot {
        Slot { tipe, lifetime }
    }
}

impl Display for Slot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{}> '{}", self.tipe, self.lifetime)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Env(pub HashMap<Ident, Slot>);

impl Env {
    pub fn default() -> Env {
        Env(HashMap::new())
    }
}

impl Display for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            return write!(f, "{{}}");
        }
        write!(f, "{{\n")?;
        for (k, v) in self.0.iter() {
            write!(f, "    {} → {}\n", k, v)?;
        }
        write!(f, "}}")
    }
}

#[derive(Debug, PartialEq)]
pub enum Error {
    UnknownVar(String),
    CannotDeref(Type),
    MovedOut(Lval),
    MoveBehindRef(Lval),
    UpdateBehindImmRef(Lval),
    CopyAfterMutBorrow(Lval),
    MoveAfterBorrow(Lval),
    MutBorrowBehindImmRef(Lval),
    MutBorrowAfterBorrow(Lval),
    BorrowAfterMutBorrow(Lval),
    Shadowing(String),
    IncompatibleTypes(Type, Type),
    LifetimeTooShort(Expr),
    AssignAfterBorrow(Lval),
    IllTypedAssertion(Type, Type),
}

pub type TypeResult<T> = Result<T, Error>;

impl Env {
    pub fn insert(&mut self, var: &str, tipe: Type, lifetime: Lifetime) {
        let t = tipe.clone();
        self.0.insert(var.to_owned(), Slot { tipe, lifetime });
        println!(
            "context after insert({} → <{}> '{}): {}",
            var, t, lifetime, self
        );
    }

    pub fn type_lval(&self, lval: &Lval) -> TypeResult<Slot> {
        let (t, lifetime) = self.type_lval_inner(&lval.ident, lval.derefs)?;
        Ok(Slot {
            tipe: t.to_owned(),
            lifetime,
        })
    }

    fn type_lval_inner(&self, ident: &Ident, derefs: usize) -> TypeResult<(&Type, Lifetime)> {
        if derefs == 0 {
            let Slot { tipe, lifetime } = self
                .0
                .get(ident)
                .ok_or(Error::UnknownVar(ident.to_owned()))?;
            Ok((tipe, *lifetime))
        } else {
            match self.type_lval_inner(ident, derefs - 1)? {
                (Type::Box(t), l) => Ok((t, l)),
                (Type::Ref(lval, ..), ..) => self.type_lval_inner(&lval.ident, lval.derefs),
                (Type::Undefined(_), ..) => Err(Error::MovedOut(Lval {
                    ident: ident.to_owned(),
                    derefs,
                })),
                (t, _) => Err(Error::CannotDeref(t.to_owned())),
            }
        }
    }

    // Returns the type under the boxes of a type, given that the
    // underlying type is defined
    pub fn contained(&self, var: &str) -> Option<&Type> {
        let s = self.0.get(var)?;
        self.contained_inner(&s.tipe)
    }
    fn contained_inner<'a>(&self, tipe: &'a Type) -> Option<&'a Type> {
        match tipe {
            t @ Type::Unit | t @ Type::Int | t @ Type::Ref(..) => Some(&t),
            Type::Box(t) => self.contained_inner(t),
            _ => None,
        }
    }

    pub fn read_prohibited(&self, lval: &Lval) -> bool {
        self.0.keys().any(|x| match self.contained(x) {
            Some(Type::Ref(u, Mutable::Yes)) => u.ident == lval.ident,
            _ => false,
        })
    }

    pub fn write_prohibited(&self, lval: &Lval) -> bool {
        self.read_prohibited(lval)
            || self.0.keys().any(|x| match self.contained(x) {
                Some(Type::Ref(u, Mutable::No)) => u.ident == lval.ident,
                _ => false,
            })
    }

    // "move" is a keyword in Rust
    pub fn moove(&mut self, lval: &Lval) -> TypeResult<()> {
        let slot = self
            .0
            .get_mut(&lval.ident)
            .ok_or(Error::UnknownVar(lval.ident.to_owned()))?;

        // refers to the value we need to wrap in undefined
        let mut t = &mut slot.tipe;

        // for each deref level, move the mutable reference inward one box
        for _ in 0..lval.derefs {
            match t {
                Type::Box(t2) => {
                    t = t2;
                }
                Type::Ref(..) => return Err(Error::MoveBehindRef(lval.to_owned())),
                t => return Err(Error::CannotDeref(t.to_owned())),
            }
        }

        // We want to do:
        // *t = Type::undefined(*t);
        // but we can't move out of *t even though we're moving it back in.
        // To solve this, we temporarily replace *t with a dummy value to get
        // ownership of *t then rewrap the old value in undefined and assign it back to t

        let old_t = mem::replace(t, Type::Unit);
        *t = Type::undefined(old_t);

        println!("context after move({lval}): {self}");

        Ok(())
    }

    // so is "mut"
    pub fn muut(&self, lval: &Lval) -> bool {
        let slot = self.0.get(&lval.ident).expect("slot should be present");
        self.mutable(lval.derefs, &slot.tipe)
    }

    fn mutable(&self, derefs: usize, tipe: &Type) -> bool {
        if derefs == 0 {
            return true;
        }
        match tipe {
            Type::Box(t) => self.mutable(derefs - 1, t),
            Type::Ref(lval, Mutable::Yes) => {
                let slot = self.0.get(&lval.ident).expect("slot should be present");
                self.mutable(lval.derefs + derefs - 1, &slot.tipe)
            }
            _ => false,
        }
    }

    pub fn compatible(&self, t1: &Type, t2: &Type) -> bool {
        match (t1, t2) {
            (Type::Int, Type::Int) | (Type::Unit, Type::Unit) => true,
            (Type::Box(t1), Type::Box(t2)) => self.compatible(t1, t2),
            (Type::Undefined(t), _) => self.compatible(t, t2),
            (_, Type::Undefined(t)) => self.compatible(t1, t),
            (Type::Ref(lval1, m1), Type::Ref(lval2, m2)) if m1 == m2 => {
                let t1 = self.type_lval(lval1).expect("should be well typed").tipe;
                let t2 = self.type_lval(lval2).expect("should be well typed").tipe;
                self.compatible(&t1, &t2)
            }
            _ => false,
        }
    }

    pub fn write(&mut self, w: &Lval, tipe: Type) -> TypeResult<()> {
        let t = tipe.clone();
        let res = self.write_inner(&w.ident, w.derefs, tipe);
        println!("context after write({w}, {t}): {self}");
        res
    }

    fn write_inner(&mut self, ident: &Ident, derefs: usize, tipe: Type) -> TypeResult<()> {
        // we need to remove and reinsert the slot because get_mut would mutably borrow self meaning we can't pass self to update.
        let (x, mut slot) = self
            .0
            .remove_entry(ident)
            .ok_or(Error::UnknownVar(ident.to_owned()))?;

        slot.tipe = self.update(derefs, slot.tipe, tipe)?;

        assert!(self.0.insert(x, slot).is_none());
        Ok(())
    }

    fn update(&mut self, derefs: usize, t1: Type, t2: Type) -> TypeResult<Type> {
        if derefs == 0 {
            return Ok(t2);
        }
        match t1 {
            Type::Box(t) => {
                let t_prime = self.update(derefs - 1, *t, t2)?;
                Ok(Type::boxx(t_prime))
            }
            Type::Ref(lval, Mutable::Yes) => {
                self.write_inner(&lval.ident, lval.derefs + derefs - 1, t2)?;
                Ok(Type::mut_ref(lval))
            }
            _ => Err(Error::CannotDeref(t1)),
        }
    }

    pub fn drop(&mut self, l: Lifetime) {
        let res = self.0.retain(|_, s| s.lifetime != l);
        println!("context after drop('{l}): {self}");
        res
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Context {
    pub env: Env,
    lifetimes: Vec<Lifetime>,
}
impl Context {
    pub fn default() -> Self {
        Context {
            env: Env::default(),
            lifetimes: vec![Lifetime::global()],
        }
    }

    // l ≥ m, the ordering relation on liftimes (Note (2) pg. 13)
    fn lifetime_contains(&self, l: Lifetime, m: Lifetime) -> bool {
        let l_pos = self
            .lifetimes
            .iter()
            .position(|lt| *lt == l)
            .expect("l should be in stack");

        let m_pos = self
            .lifetimes
            .iter()
            .position(|lt| *lt == m)
            .expect("m should be in stack");

        l_pos <= m_pos
    }

    // Γ ⊢ T ≥ l (Definition 3.21)
    fn well_formed(&self, tipe: &Type, l: Lifetime) -> bool {
        match tipe {
            Type::Int | Type::Unit => true,
            Type::Box(t) => self.well_formed(t, l),
            Type::Ref(lval, ..) => {
                let Slot { lifetime: m, .. } =
                    self.env.type_lval(lval).expect("should be well typed");
                return self.lifetime_contains(m, l);
            }
            _ => {
                panic!("unexpected type")
            }
        }
    }

    pub fn type_expr(&mut self, expr: &mut Expr) -> TypeResult<Type> {
        print!("'{:4}", format!("{}", self.lifetimes.last().unwrap()));
        print!("typing expr: {} ", expr);
        let res;
        match expr {
            Expr::Unit => {
                println!("(T-Unit)");
                res = Type::Unit
            }
            Expr::Int(_) => {
                println!("(T-Int)");
                res = Type::Int
            }
            Expr::Lval(lval, copyable) => {
                self.env
                    .contained(&lval.ident)
                    .ok_or(Error::MovedOut(lval.to_owned()))?;

                let Slot { tipe, .. } = self.env.type_lval(lval)?;

                match tipe {
                    Type::Int | Type::Unit | Type::Ref(.., Mutable::No) => {
                        *copyable = Copyable::Yes;

                        println!("(T-Copy)");

                        (!self.env.read_prohibited(lval))
                            .then(|| ())
                            .ok_or(Error::CopyAfterMutBorrow(lval.to_owned()))?;

                        res = tipe
                    }
                    _ => {
                        *copyable = Copyable::No;

                        println!("(T-Move)");

                        (!self.env.write_prohibited(lval))
                            .then(|| ())
                            .ok_or(Error::MoveAfterBorrow(lval.to_owned()))?;

                        self.env.moove(lval)?;

                        res = tipe
                    }
                }
            }
            Expr::Box(expr) => {
                println!("(T-Box)");

                let t = self.type_expr(expr)?;
                res = Type::boxx(t);
            }
            Expr::AssertEq(e1, e2) => {
                println!("(T-AssertEq)");
                match (self.type_expr(e1)?, self.type_expr(e2)?) {
                    (Type::Int, Type::Int) | (Type::Unit, Type::Unit) => res = Type::Unit,
                    (t1, t2) => return Err(Error::IllTypedAssertion(t1, t2)),
                }
            }
            Expr::Borrow(lval, Mutable::Yes) => {
                println!("(T-MutBorrow)");

                if matches!(self.env.type_lval(lval)?.tipe, Type::Undefined(..)) {
                    return Err(Error::MovedOut(lval.to_owned()));
                }

                self.env
                    .muut(lval)
                    .then(|| ())
                    .ok_or(Error::MutBorrowBehindImmRef(lval.to_owned()))?;

                (!self.env.write_prohibited(lval))
                    .then(|| ())
                    .ok_or(Error::MutBorrowAfterBorrow(lval.to_owned()))?;

                res = Type::mut_ref(lval.to_owned());
            }
            Expr::Borrow(lval, Mutable::No) => {
                println!("(T-ImmBorrow)");

                if matches!(self.env.type_lval(lval)?.tipe, Type::Undefined(..)) {
                    return Err(Error::MovedOut(lval.to_owned()));
                }

                (!self.env.read_prohibited(lval))
                    .then(|| ())
                    .ok_or(Error::BorrowAfterMutBorrow(lval.to_owned()))?;

                res = Type::imm_ref(lval.to_owned());
            }
            Expr::Block(stmts, expr, lifetime) => {
                println!("(T-Block)");

                print!("'{:4}", format!("{}", self.lifetimes.last().unwrap()));
                self.lifetimes.push(*lifetime);
                println!("enter block '{lifetime}");
                println!();
                for stmt in stmts {
                    self.type_stmt(stmt)?;
                }
                let t = self.type_expr(expr)?;

                self.well_formed(&t, *lifetime)
                    .then(|| ())
                    .ok_or(Error::LifetimeTooShort(*expr.to_owned()))?;

                print!("'{:4}", format!("{}", self.lifetimes.last().unwrap()));
                println!("exit block '{lifetime}");

                assert_eq!(
                    self.lifetimes.pop().expect("should have current lifetime"),
                    *lifetime
                );
                self.env.drop(*lifetime);

                println!();

                res = t;
            }
        }
        print!("'{:4}", format!("{}", self.lifetimes.last().unwrap()));
        println!("typed expr {expr} : {res}");
        Ok(res)
    }

    pub fn type_stmt(&mut self, stmt: &mut Stmt) -> TypeResult<()> {
        print!("'{:4}", format!("{}", self.lifetimes.last().unwrap()));
        print!("typing stmt: {} ", stmt);
        match stmt {
            Stmt::Assign(lval, expr) => {
                println!("(T-Assign)");

                let Slot {
                    tipe: t1,
                    lifetime: m,
                } = self.env.type_lval(lval)?;

                print!("'{:4}", format!("{}", self.lifetimes.last().unwrap()));
                println!("typed lval {lval} : {t1}");

                let t2 = self.type_expr(expr)?;

                assert!(!matches!(t2, Type::Undefined(..)), "expr is undefined");

                self.env
                    .compatible(&t1, &t2)
                    .then(|| ())
                    .ok_or(Error::IncompatibleTypes(t1, t2.to_owned()))?;

                self.well_formed(&t2, m)
                    .then(|| ())
                    .ok_or(Error::LifetimeTooShort(expr.to_owned()))?;

                self.env
                    .write(lval, t2)
                    .or(Err(Error::UpdateBehindImmRef(lval.to_owned())))?;

                (!self.env.write_prohibited(lval))
                    .then(|| ())
                    .ok_or(Error::AssignAfterBorrow(lval.to_owned()))?;

                Ok(())
            }
            Stmt::LetMut(x, expr) => {
                println!("(T-Declare)");

                (!self.env.0.contains_key(x))
                    .then(|| ())
                    .ok_or(Error::Shadowing(x.to_owned()))?;

                let t = self.type_expr(expr)?;

                self.env.insert(
                    x,
                    t,
                    *self.lifetimes.last().expect("should have current lifetime"),
                );

                Ok(())
            }
            Stmt::Expr(expr) => {
                println!();
                self.type_expr(expr)?;

                Ok(())
            }
        }
    }
}
