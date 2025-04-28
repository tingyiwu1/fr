use fr::{
    eval,
    types::{self, Env, Slot, Type},
    utils::{Copyable, Expr, Lifetime, Lval, Mutable, Stmt},
};

fn expr1() -> (Expr, Lifetime) {
    let m = Lifetime(1);
    let l = Lifetime(2);
    (
        Expr::Block(
            vec![
                Stmt::let_mut("x", Expr::Int(1)),
                Stmt::let_mut(
                    "y",
                    Expr::Box(Box::new(Expr::Lval(Lval::var("x"), Copyable::Yes))),
                ),
            ],
            Box::new(Expr::Block(
                vec![
                    Stmt::let_mut("z", Expr::Box(Box::new(Expr::Int(0)))),
                    Stmt::Assign(Lval::var("y"), Expr::Borrow(Lval::var("z"), Mutable::No)),
                    Stmt::Assign(Lval::var("y"), Expr::Lval(Lval::var("z"), Copyable::No)),
                ],
                Box::new(Expr::Lval(Lval::deref(1, "y"), Copyable::No)),
                m,
            )),
            l,
        ),
        l,
    )
}

fn type1() {
    let mut context = types::Context::default();
    let (mut expr, ..) = expr1();
    let t = context.type_expr(&mut expr);
    dbg!(&t);
}

fn eval1() {
    let mut context = eval::Context::default();
    let (expr, l) = expr1();
    let r = context.eval_expr(&expr, l);
    dbg!(r);
}

fn test2() {
    let mut context = eval::Context::default();
    let m = Lifetime(1);
    let l = Lifetime(2);
    let expr = Expr::Block(
        vec![
            Stmt::let_mut("x", Expr::Box(Box::new(Expr::Int(0)))),
            Stmt::Expr(Expr::Block(
                vec![
                    Stmt::let_mut("y", Expr::Borrow(Lval::var("x"), Mutable::Yes)),
                    Stmt::Assign(Lval::deref(1, "y"), Expr::Box(Box::new(Expr::Int(1)))),
                ],
                Box::new(Expr::Unit),
                m,
            )),
            Stmt::let_mut("z", Expr::Lval(Lval::var("x"), Copyable::No)),
        ],
        Box::new(Expr::Lval(Lval::deref(1, "z"), Copyable::No)),
        l,
    );
    let r = context.eval_expr(&expr, l);
    dbg!(r);
}

fn expr3() -> (Expr, Lifetime) {
    let m = Lifetime(1);
    (
        Expr::Block(
            vec![
                Stmt::let_mut("a", Expr::boxx(Expr::Int(1))),
                Stmt::let_mut("b", Expr::boxx(Expr::Int(2))),
                Stmt::let_mut("c", Expr::boxx(Expr::Int(3))),
                Stmt::let_mut("x", Expr::Borrow(Lval::var("a"), Mutable::Yes)),
                Stmt::Assign(Lval::new("x", 2), Expr::Int(4)),
                Stmt::Assign(
                    Lval::new("x", 2),
                    Expr::Lval(Lval::new("b", 1), Copyable::No),
                ),
                Stmt::Assign(Lval::new("x", 2), Expr::Int(5)),
                Stmt::Assign(Lval::new("x", 1), Expr::Lval(Lval::var("c"), Copyable::No)),
                Stmt::Assign(Lval::new("x", 2), Expr::Int(6)),
            ],
            Box::new(Expr::Unit),
            m,
        ),
        m,
    )
}

fn type3() {
    let mut context = types::Context::default();
    let (mut expr, ..) = expr3();
    let t = context.type_expr(&mut expr);
    dbg!(&t);
}

fn eval3() {
    let mut context = eval::Context::default();
    let (expr, l) = expr3();
    let r = context.eval_expr(&expr, l);
    dbg!(r);
}

fn expr4() -> (Expr, Lifetime) {
    let l = Lifetime(1);
    (
        Expr::block(
            vec![
                Stmt::let_mut("x", Expr::boxx(Expr::Int(0))),
                Stmt::let_mut("y", Expr::Lval(Lval::var("x"), Copyable::No)),
            ],
            l,
        ),
        l,
    )
}

fn expr5() -> (Expr, Lifetime) {
    let l = Lifetime(1);
    (
        Expr::block(
            vec![
                Stmt::let_mut("x", Expr::boxx(Expr::boxx(Expr::Int(0)))),
                Stmt::let_mut("y", Expr::Lval(Lval::new("x", 1), Copyable::No)),
            ],
            l,
        ),
        l,
    )
}

fn expr6() -> (Expr, Lifetime) {
    let l = Lifetime(1);
    (
        Expr::block(
            vec![
                Stmt::let_mut("x", Expr::Int(0)),
                Stmt::let_mut("y", Expr::Lval(Lval::var("x"), Copyable::No)),
                Stmt::Assign(Lval::var("x"), Expr::Int(0)),
            ],
            l,
        ),
        l,
    )
}

fn tipe((mut expr, ..): (Expr, Lifetime)) {
    let mut context = types::Context::default();
    let t = context.type_expr(&mut expr);
    dbg!(&t);
}

fn main() {
    tipe(expr6())
}
