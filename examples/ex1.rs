// fn main() {}
//
fn main() {
    let mut a = {10};
    let mut b = {1; {2; {3; 4}}}; // sf
    let mut c = {
      let mut d = Box::new({
        let mut e = Box::new(3);
        b = *e;
        ();
        e
      });
      d
    };
    {
      let mut g = {
        *c = {
          let mut f = Box::new(&mut a);
          {
            **f = 11;
          }
          {();}
          {
            b = 5;
            Box::new(b)
          }
        };
      };
    }
    assert_eq!({
      **c = 6;
      b = 6;
      a
    }, {
      assert_eq!(**c, b);
      11
    });
}
// sdfjsdf
