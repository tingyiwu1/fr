fn main() {
    let mut a = 3;
    let mut b = 4;
    let mut w = Box::new(Box::new(Box::new(&a)));
    let mut z = &mut **w;
    let mut y = Box::new(&mut *z);
    let mut x = Box::new(Box::new(&mut **y));

    // let d = ***x;

    ***x = Box::new(&b);
}
