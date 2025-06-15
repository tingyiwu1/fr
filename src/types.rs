use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    mem,
};

use crate::utils::{Copyable, Expr, Ident, Lifetime, Lval, Mutable, Stmt};

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    Unit,
    Int,
    Bool,
    Box(Box<Type>),
    Ref(HashSet<Lval>, Mutable),
    Undefined(Box<Type>),
}

fn fmt_lvals(lvals: &HashSet<Lval>) -> String {
    lvals
        .iter()
        .map(|lv| format!("{}", lv))
        .collect::<Vec<_>>()
        .join(",")
}

impl Type {
    pub fn boxx(tipe: Type) -> Type {
        Type::Box(Box::new(tipe))
    }
    pub fn imm_ref(lval: Lval) -> Type {
        Type::Ref(HashSet::from([lval]), Mutable::No)
    }
    pub fn mut_ref(lval: Lval) -> Type {
        Type::Ref(HashSet::from([lval]), Mutable::Yes)
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
            Type::Bool => write!(f, "bool"),
            Type::Box(t) => write!(f, "□{}", t),
            Type::Ref(lvals, Mutable::Yes) => write!(f, "&mut {}", fmt_lvals(lvals)),
            Type::Ref(lvals, Mutable::No) => write!(f, "&{}", fmt_lvals(lvals)),
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
pub struct Env {
    pub map: HashMap<Ident, Slot>,
    pub fresh_var: usize,
    pub lifetimes: Vec<Lifetime>,
}

impl Display for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.map.is_empty() {
            return write!(f, "{{}}");
        }
        write!(f, "{{\n")?;
        for (k, v) in self.map.iter() {
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
    IllTypedIfCond(Type),
    CannotCopy(Type),
}

pub type TypeResult<T> = Result<T, Error>;

impl Env {
    pub fn default() -> Env {
        Env {
            map: HashMap::new(),
            fresh_var: 0,
            lifetimes: vec![Lifetime::global()],
        }
    }

    fn fresh_var(&mut self) -> Ident {
        self.fresh_var += 1;
        self.fresh_var.to_string()
    }

    pub fn insert(&mut self, var: &str, tipe: Type, lifetime: Lifetime) {
        let t = tipe.clone();
        self.map.insert(var.to_owned(), Slot { tipe, lifetime });
        println!(
            "context after insert({} → <{}> '{}): {}",
            var, t, lifetime, self
        );
    }

    pub fn join(&self, t1: Type, t2: Type) -> TypeResult<Type> {
        // println!("joining {t1} {t2}");

        match (t1, t2) {
            (t1, t2) if t1 == t2 => Ok(t1),
            (Type::Undefined(t1), Type::Undefined(t2)) => Ok(Type::undefined(self.join(*t1, *t2)?)),
            (Type::Box(t1), Type::Box(t2)) => Ok(Type::boxx(self.join(*t1, *t2)?)),
            (t1, Type::Undefined(t2)) => {
                let j = match (t1, *t2) {
                    (Type::Box(t1), Type::Box(t2)) => {
                        let j = Type::boxx(self.join(*t1, Type::Undefined(t2))?);
                        Type::boxx(j)
                    }
                    (t1, t2) => self.join(t1, t2)?,
                };
                Ok(Type::undefined(j))
            }
            (t1 @ Type::Undefined(..), t2) => self.join(t2, t1),
            (Type::Ref(lvals1, m1), Type::Ref(lvals2, m2)) if m1 == m2 => {
                Ok(Type::Ref(lvals1.union(&lvals2).cloned().collect(), m1))
            }
            (t1, t2) => Err(Error::IncompatibleTypes(t1, t2)),
        }
    }

    pub fn join_env(&mut self, other: &mut Self) -> TypeResult<()> {
        // dom(Γ1) = dom(Γ2)
        // println!("joining");
        // println!("{self}");
        // println!("{other}");
        assert!(
            self.map.len() == other.map.len() && self.map.keys().all(|k| other.map.contains_key(k)),
            "joining envs with different domains"
        );

        for k in self.map.keys().cloned().collect::<Vec<_>>() {
            let mut s1 = self.map.remove(&k).expect("should have key");
            let s2 = other.map.remove(&k).expect("other should have same domain");
            let n = self.join(s1.tipe, s2.tipe)?;
            s1.tipe = n;
            self.map.insert(k, s1);
        }
        assert!(other.map.len() == 0, "leftover item in other");

        println!("context after join env: {}", self);

        Ok(())
    }

    // l ≥ m, the ordering relation on liftimes (Note (2) pg. 13)
    pub fn lifetime_contains(&self, l: Lifetime, m: Lifetime) -> bool {
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

    pub fn type_lval(&self, lval: &Lval) -> TypeResult<Slot> {
        let (tipe, lifetime) = self.type_lval_inner(&lval.ident, lval.derefs)?;
        Ok(Slot { tipe, lifetime })
    }

    fn type_lval_inner(&self, ident: &Ident, derefs: usize) -> TypeResult<(Type, Lifetime)> {
        if derefs == 0 {
            let Slot { tipe, lifetime } = self
                .map
                .get(ident)
                .ok_or(Error::UnknownVar(ident.to_owned()))?;
            Ok((tipe.to_owned(), *lifetime))
        } else {
            match self.type_lval_inner(ident, derefs - 1)? {
                (Type::Box(t), l) => Ok((*t, l)),
                (Type::Ref(lvals, ..), ..) => {
                    assert!(lvals.len() > 0);

                    let v = lvals
                        .iter()
                        .map(|lval| self.type_lval_inner(&lval.ident, lval.derefs))
                        .collect::<Result<Vec<_>, _>>()?;

                    let mut res_t = v[0].0.clone();
                    let mut res_l = v[0].1;

                    for (t, l) in v.into_iter().skip(1) {
                        res_t = self.join(res_t, t.clone())?;
                        if self.lifetime_contains(res_l, l) {
                            res_l = l;
                        }
                    }

                    Ok((res_t, res_l))
                }
                // (t @ Type::Undefined(..), l) => Ok((t, l)),
                (t, _) => Err(Error::CannotDeref(t)),
            }
        }
    }

    // Returns the type under the boxes of a type, given that the
    // underlying type is defined
    pub fn contained(&self, var: &str) -> Option<&Type> {
        let s = self.map.get(var)?;
        self.contained_inner(&s.tipe)
    }
    fn contained_inner<'a>(&self, tipe: &'a Type) -> Option<&'a Type> {
        match tipe {
            t @ Type::Unit | t @ Type::Int | t @ Type::Bool | t @ Type::Ref(..) => Some(&t),
            Type::Box(t) => self.contained_inner(t),
            _ => None,
        }
    }

    pub fn read_prohibited(&self, lval: &Lval) -> bool {
        self.map.keys().any(|x| match self.contained(x) {
            Some(Type::Ref(lvals, Mutable::Yes)) => lvals.iter().any(|lv| lv.ident == lval.ident),
            _ => false,
        })
    }

    pub fn write_prohibited(&self, lval: &Lval) -> bool {
        self.read_prohibited(lval)
            || self.map.keys().any(|x| match self.contained(x) {
                Some(Type::Ref(lvals, Mutable::No)) => {
                    lvals.iter().any(|lv| lv.ident == lval.ident)
                }
                _ => false,
            })
    }

    // "move" is a keyword in Rust
    pub fn moove(&mut self, lval: &Lval) -> TypeResult<()> {
        let slot = self
            .map
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
        let slot = self.map.get(&lval.ident).expect("slot should be present");
        self.mutable(lval.derefs, &slot.tipe)
    }

    fn mutable(&self, derefs: usize, tipe: &Type) -> bool {
        if derefs == 0 {
            return true;
        }
        match tipe {
            Type::Box(t) => self.mutable(derefs - 1, t),
            Type::Ref(lvals, Mutable::Yes) => lvals.iter().all(|lval| {
                let slot = self.map.get(&lval.ident).expect("slot should be present");
                self.mutable(lval.derefs + derefs - 1, &slot.tipe)
            }),
            _ => false,
        }
    }

    pub fn compatible(&self, t1: &Type, t2: &Type) -> TypeResult<bool> {
        // println!("compatible({t1} | {t2})");
        match (t1, t2) {
            (Type::Int, Type::Int) | (Type::Unit, Type::Unit) | (Type::Bool, Type::Bool) => {
                Ok(true)
            }
            (Type::Box(t1), Type::Box(t2)) => self.compatible(t1, t2),
            (Type::Undefined(t), _) => self.compatible(t, t2),
            (_, Type::Undefined(t)) => self.compatible(t1, t),
            (Type::Ref(lvals1, m1), Type::Ref(lvals2, m2)) if m1 == m2 => {
                for lval1 in lvals1 {
                    for lval2 in lvals2 {
                        // println!("{lval1}, {lval2}");
                        let t1 = self.type_lval(lval1)?.tipe;
                        let t2 = self.type_lval(lval2)?.tipe;
                        // println!("{t1}, {t2}");
                        if !self.compatible(&t1, &t2)? {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    pub fn write(&mut self, w: &Lval, tipe: Type) -> TypeResult<()> {
        let t = tipe.clone();
        // println!("write({w}, {t})");
        let res = self.write_inner(0, &w.ident, w.derefs, tipe);
        println!("context after write({w}, {t}): {self}");
        res
    }

    fn write_inner(
        &mut self,
        rank: usize,
        ident: &Ident,
        derefs: usize,
        tipe: Type,
    ) -> TypeResult<()> {
        // println!("write_inner({rank}, {ident}, {derefs}, {tipe})");
        let slot = self
            .map
            .get(ident)
            .ok_or(Error::UnknownVar(ident.to_owned()))?;

        let new = self.update(rank, derefs, slot.tipe.clone(), tipe)?;

        self.map.get_mut(ident).expect("should be present").tipe = new;

        Ok(())
    }

    fn update(&mut self, rank: usize, derefs: usize, t1: Type, t2: Type) -> TypeResult<Type> {
        // let signal = format!("update({rank}, {derefs}, {t1}, {t2})");
        // println!("{signal}");
        if derefs == 0 {
            if rank == 0 {
                return Ok(t2);
            }
            return self.join(t1, t2);
        }
        let res = match t1 {
            Type::Box(t) => {
                let t_prime = self.update(rank, derefs - 1, *t, t2)?;
                // print!("{signal} ");
                // println!("t_prime: {t_prime}");
                Type::boxx(t_prime)
            }
            Type::Ref(lvals, Mutable::Yes) => {
                for lval in lvals.iter().cloned() {
                    let mut new = self.clone();
                    new.write_inner(rank + 1, &lval.ident, lval.derefs + derefs - 1, t2.clone())?;
                    self.join_env(&mut new)?;
                }

                Type::Ref(lvals, Mutable::Yes)
            }
            _ => return Err(Error::CannotDeref(t1)),
        };
        // println!("env after {signal}: {self}");
        Ok(res)
    }

    pub fn drop(&mut self, l: Lifetime) {
        let res = self.map.retain(|_, s| s.lifetime != l);
        println!("context after drop('{l}): {self}");
        res
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Context {
    pub env: Env,
}
impl Context {
    pub fn default() -> Self {
        Context {
            env: Env::default(),
        }
    }

    // Γ ⊢ T ≥ l (Definition 3.21)
    fn well_formed(&self, tipe: &Type, l: Lifetime) -> bool {
        match tipe {
            Type::Int | Type::Unit | Type::Bool => true,
            Type::Box(t) => self.well_formed(t, l),
            Type::Ref(lvals, ..) => lvals.iter().all(|lval| {
                let Slot { lifetime: m, .. } =
                    self.env.type_lval(lval).expect("should be well typed");
                self.env.lifetime_contains(m, l)
            }),
            _ => {
                panic!("unexpected type")
            }
        }
    }

    pub fn type_expr(&mut self, expr: &mut Expr) -> TypeResult<Type> {
        print!("'{:4}", format!("{}", self.env.lifetimes.last().unwrap()));
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
            Expr::Bool(_) => {
                println!("(T-Bool)");
                res = Type::Bool
            }
            Expr::Equals(e1, e2) => {
                println!("(T-Equal)");

                let t1 = self.type_expr(e1)?;
                let gamma = self.env.fresh_var();

                self.env.insert(
                    &gamma,
                    t1,
                    *self
                        .env
                        .lifetimes
                        .last()
                        .expect("should have current lifetime"),
                );

                let t2 = self.type_expr(e2)?;

                let Slot { tipe: t1, .. } = self.env.map.remove(&gamma).expect("should be present");

                self.env
                    .compatible(&t1, &t2)?
                    .then(|| ())
                    .ok_or(Error::IncompatibleTypes(t1.to_owned(), t2.to_owned()))?;

                matches!(
                    t1,
                    Type::Int | Type::Unit | Type::Bool | Type::Ref(.., Mutable::No)
                )
                .then(|| ())
                .ok_or(Error::CannotCopy(t1))?;

                matches!(
                    t2,
                    Type::Int | Type::Unit | Type::Bool | Type::Ref(.., Mutable::No)
                )
                .then(|| ())
                .ok_or(Error::CannotCopy(t2))?;

                res = Type::Bool
            }
            Expr::Lval(lval, copyable) => {
                self.env
                    .contained(&lval.ident)
                    .ok_or(Error::MovedOut(lval.to_owned()))?;

                let Slot { tipe, .. } = self.env.type_lval(lval)?;

                match tipe {
                    Type::Int | Type::Unit | Type::Bool | Type::Ref(.., Mutable::No) => {
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
                    (Type::Int, Type::Int)
                    | (Type::Unit, Type::Unit)
                    | (Type::Bool, Type::Bool) => res = Type::Unit,
                    (t1, t2) => return Err(Error::IllTypedAssertion(t1, t2)),
                }
            }
            Expr::IfElse { cond, t, f } => {
                println!("(T-If)");

                let c = self.type_expr(cond)?;

                (c == Type::Bool)
                    .then(|| ())
                    .ok_or(Error::IllTypedIfCond(c))?;

                let mut ctx2 = self.clone();

                let t1 = self.type_expr(t)?;
                let t2 = ctx2.type_expr(f)?;

                self.env.join_env(&mut ctx2.env)?;

                res = self.env.join(t1, t2)?;
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

                print!("'{:4}", format!("{}", self.env.lifetimes.last().unwrap()));
                self.env.lifetimes.push(*lifetime);
                println!("enter block '{lifetime}");
                println!();
                for stmt in stmts {
                    self.type_stmt(stmt)?;
                }
                let t = self.type_expr(expr)?;

                self.well_formed(&t, *lifetime)
                    .then(|| ())
                    .ok_or(Error::LifetimeTooShort(*expr.to_owned()))?;

                print!("'{:4}", format!("{}", self.env.lifetimes.last().unwrap()));
                println!("exit block '{lifetime}");

                assert_eq!(
                    self.env
                        .lifetimes
                        .pop()
                        .expect("should have current lifetime"),
                    *lifetime
                );
                self.env.drop(*lifetime);

                println!();

                res = t;
            }
        }
        print!("'{:4}", format!("{}", self.env.lifetimes.last().unwrap()));
        println!("typed expr {expr} : {res}");
        Ok(res)
    }

    pub fn type_stmt(&mut self, stmt: &mut Stmt) -> TypeResult<()> {
        print!("'{:4}", format!("{}", self.env.lifetimes.last().unwrap()));
        print!("typing stmt: {} ", stmt);
        match stmt {
            Stmt::Assign(lval, expr) => {
                println!("(T-Assign)");

                let Slot {
                    tipe: t1,
                    lifetime: m,
                } = self.env.type_lval(lval)?;

                print!("'{:4}", format!("{}", self.env.lifetimes.last().unwrap()));
                println!("typed lval {lval} : {t1}");

                let t2 = self.type_expr(expr)?;

                assert!(!matches!(t2, Type::Undefined(..)), "expr is undefined");

                self.env
                    .compatible(&t1, &t2)?
                    .then(|| ())
                    .ok_or(Error::IncompatibleTypes(t1, t2.to_owned()))?;

                self.well_formed(&t2, m)
                    .then(|| ())
                    .ok_or(Error::LifetimeTooShort(expr.to_owned()))?;

                self.env
                    .write(lval, t2)
                    .or(Err(Error::UpdateBehindImmRef(lval.to_owned())))?;

                println!("after write");

                (!self.env.write_prohibited(lval))
                    .then(|| ())
                    .ok_or(Error::AssignAfterBorrow(lval.to_owned()))?;

                Ok(())
            }
            Stmt::LetMut(x, expr) => {
                println!("(T-Declare)");

                (!self.env.map.contains_key(x))
                    .then(|| ())
                    .ok_or(Error::Shadowing(x.to_owned()))?;

                let t = self.type_expr(expr)?;

                self.env.insert(
                    x,
                    t,
                    *self
                        .env
                        .lifetimes
                        .last()
                        .expect("should have current lifetime"),
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
