fn main() {
    let mut a = 0;
    let mut x = 0;
    let mut y = 0;
    let mut p = &mut x;
    let mut q = &mut y;

    if true {
        p = &mut a;
    } else {
        q = &mut a;
    };
    *p = 3;
    *q = 4;
}
