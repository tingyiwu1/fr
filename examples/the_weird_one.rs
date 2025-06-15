fn main() {
    let mut a = 4;
    let mut x = &mut a;

    let mut b = if true {
        {
            x;
        }
        &a
    } else {
        &*x
    };
    b = &a;
}
