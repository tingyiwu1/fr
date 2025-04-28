fn main() {
    let mut x = -01245345;
    let mut y = Box::new(x);

    let mut a = { *y = 3 };

    let mut b = {
        let mut f = 3;
        {};
    };

    let mut c = { () };

    let mut d = {
        ();
        ();
        3
    };

    let mut w = {
        let mut z = &mut x;
        *y = 3;
        z
    };
    w;
    x;
}
