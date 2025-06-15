fn main() {
    let mut a = Box::new(1);
    let mut b = 2;
    let mut x = Box::new(&*a);
    let mut y = &mut *x;
    *y = &b;

    // *x = &b;
    // b = 3;
    // *a = 3;

    *y;
}
