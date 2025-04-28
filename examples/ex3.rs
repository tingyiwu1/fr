fn main() {
    let mut x = 0;
    let mut y = &x;
    {
        let mut z = 1;
        y = &z; // z does not live long enough
    }
    x;
    // y;
}
