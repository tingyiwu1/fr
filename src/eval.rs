use std::{collections::HashMap, fmt::Display, mem};

use crate::utils::{Copyable, Expr, Ident, Lifetime, Lval, Stmt};

type Location = Ident;

#[derive(Debug, Clone, PartialEq)]
pub enum Owned {
    Yes,
    No,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Unit,
    Int(i32),
    Ref(Location, Owned),
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Unit => write!(f, "ε"),
            Value::Int(i) => write!(f, "{}", i),
            Value::Ref(loc, owned) => write!(
                f,
                "l_{} {}",
                loc,
                match owned {
                    Owned::Yes => "●",
                    Owned::No => "○",
                }
            ),
        }
    }
}

type Pvalue = Option<Value>;

fn fmt_pvalue(pv: &Pvalue) -> String {
    match pv {
        Some(v) => format!("{}", v),
        None => "⊥".to_string(),
    }
}

fn fmt_pvalues(pvalues: &[Pvalue]) -> String {
    format!(
        "[{}]",
        pvalues
            .iter()
            .map(|pv| fmt_pvalue(pv))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

#[derive(Debug, Clone, PartialEq)]
pub struct Slot {
    pub value: Pvalue,
    lifetime: Lifetime,
}

impl Display for Slot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{}> '{}", fmt_pvalue(&self.value), self.lifetime)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Store(HashMap<Location, Slot>);

impl Display for Store {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            return write!(f, "{{}}");
        }
        write!(f, "{{\n")?;
        for (k, v) in self.0.iter() {
            write!(f, "    l_{} → {}\n", k, v)?;
        }
        write!(f, "}}")
    }
}

impl<'a> Store {
    pub fn default() -> Self {
        Store(HashMap::new())
    }

    pub fn locate(&'a self, w: &'a Lval) -> &'a Location {
        self.locate_inner(&w.ident, w.derefs)
    }
    fn locate_inner(&'a self, ident: &'a Ident, derefs: usize) -> &'a Location {
        assert!(self.0.contains_key(ident), "location not in store");

        if derefs == 0 {
            return ident;
        }
        match self.0.get(ident) {
            Some(Slot {
                value: Some(Value::Ref(l, ..)),
                ..
            }) => self.locate_inner(l, derefs - 1),
            _ => panic!("tried to deref a non-ref"),
        }
    }

    pub fn read(&self, x: &Lval) -> &Slot {
        self.0
            .get(self.locate(x))
            .expect("location should have value")
    }

    pub fn write(&mut self, x: &Lval, v: Pvalue) -> Pvalue {
        let fmt_v = fmt_pvalue(&v); // for printing later

        let loc = self.locate(x).to_owned();
        let slot = self.0.get_mut(&loc).expect("location should have value");

        let res = mem::replace(&mut slot.value, v);

        println!("store after write({}, {}): {}", x, fmt_v, self);
        res
    }

    pub fn locs_by_lifetime(&self, lifetime: Lifetime) -> Vec<Pvalue> {
        self.0
            .iter()
            .filter(|(_, v)| v.lifetime == lifetime)
            .map(|(k, _)| Some(Value::Ref(k.to_owned(), Owned::Yes)))
            .collect()
    }
    pub fn drop(&mut self, values: Vec<Pvalue>) {
        self.drop_inner(&values);
        println!("store after drop({}): {}", fmt_pvalues(&values), self);
    }
    fn drop_inner(&mut self, values: &[Pvalue]) {
        match values {
            [] => return,
            [Some(Value::Ref(loc, Owned::Yes)), rest @ ..] => {
                let v = self
                    .0
                    .remove(loc)
                    .expect("should only remove existing value")
                    .value;
                self.drop_inner(&vec![v]);
                self.drop_inner(rest);
            }
            [_v, rest @ ..] => {
                self.drop_inner(rest);
            }
        }
    }

    pub fn insert(&mut self, location: &str, value: Pvalue, lifetime: Lifetime) {
        assert!(
            !self.0.contains_key(location),
            "cannot insert duplicate location"
        );

        let fmt_v = fmt_pvalue(&value);

        self.0.insert(location.to_owned(), Slot { value, lifetime });

        println!(
            "store after insert(l_{} → <{}> '{}): {}",
            location, fmt_v, lifetime, self
        );
    }
}

#[derive(Debug, Clone)]
pub struct Context {
    pub store: Store,
    fresh_id: usize,
}

impl Context {
    pub fn default() -> Self {
        Context {
            store: Store::default(),
            fresh_id: 0,
        }
    }

    fn fresh_id(&mut self) -> Ident {
        self.fresh_id += 1;
        self.fresh_id.to_string()
    }

    pub fn eval_expr(&mut self, expr: &Expr, l: Lifetime) -> Value {
        print!("'{:4}", format!("{}", l));
        print!("evaluating expr: {} ", expr);
        let res;
        match expr {
            Expr::Unit => {
                println!("(R-Unit)");
                res = Value::Unit;
            }
            Expr::Int(i) => {
                println!("(R-Int)");
                res = Value::Int(*i);
            }
            Expr::Lval(lval, copyable) => {
                res = match copyable {
                    Copyable::No => {
                        println!("(R-Move)");
                        self.store.write(lval, None)
                    }
                    Copyable::Yes => {
                        println!("(R-Copy)");
                        self.store.read(lval).value.clone()
                    }
                }
                .expect("value should not be undefined")
            }
            Expr::Box(expr) => {
                println!("(R-Box)");
                let v = self.eval_expr(expr, l);
                let location = self.fresh_id();
                self.store.insert(&location, Some(v), Lifetime::global());

                res = Value::Ref(location, Owned::Yes);
            }
            Expr::AssertEq(e1, e2) => {
                println!("(R-AssertEq)");
                let v1 = self.eval_expr(e1, l);
                let v2 = self.eval_expr(e2, l);
                assert_eq!(v1, v2);
                res = Value::Unit;
            }
            Expr::Borrow(lval, _mutable) => {
                println!("(R-Borrow)");
                let location = self.store.locate(lval);
                res = Value::Ref(location.to_owned(), Owned::No);
            }
            Expr::Block(stmts, expr, lifetime) => {
                println!("(R-Block)");
                print!("'{:4}", format!("{}", l));
                println!("enter block '{lifetime}");
                println!();

                for stmt in stmts {
                    self.eval_stmt(stmt, *lifetime);
                }
                res = self.eval_expr(expr, *lifetime);

                print!("'{:4}", format!("{}", lifetime));
                println!("exit block '{lifetime}");

                self.store.drop(self.store.locs_by_lifetime(*lifetime));

                println!();
            }
        }
        print!("'{:4}", format!("{}", l));
        println!("evaluated expr {expr} ⇓ {res}");

        res
    }
    pub fn eval_stmt(&mut self, stmt: &Stmt, l: Lifetime) {
        print!("'{:4}", format!("{}", l));
        print!("evaluating stmt: {} ", stmt);

        match stmt {
            Stmt::Assign(w, expr) => {
                println!("(R-Assign)");
                let v2 = self.eval_expr(expr, l);
                let v1 = self.store.read(w).value.to_owned();
                self.store.drop(vec![v1]);
                self.store.write(w, Some(v2));
            }
            Stmt::LetMut(x, expr) => {
                println!("(R-Declare)");
                let v = self.eval_expr(expr, l);
                self.store.insert(x, Some(v), l);
            }
            Stmt::Expr(expr) => {
                println!();
                self.eval_expr(expr, l);
            }
        }
    }
}
