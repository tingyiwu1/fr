use fr::eval;
use fr::parser::Parser;
use fr::types;
use fr::utils::*;
use std::env;
use std::fs::File;
use std::io::{Error, ErrorKind, Read};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let filename = {
        let mut args = env::args();
        args.next();
        args.next().ok_or(Error::new(
            ErrorKind::NotFound,
            "usage: cargo run --bin interp <filename>",
        ))?
    };

    let mut contents = String::new();
    File::open(filename)?.read_to_string(&mut contents)?;

    // let lexer = Lexer::new(&contents[..]);

    // lexer.take_while(|r| r.is_ok()).for_each(|t| {
    //     dbg!(&t.unwrap());
    // });

    let mut e = Parser::new(&contents[..])
        .parse()
        .map_err(|err| Error::new(ErrorKind::Other, format!("{:?}", err)))?;

    // dbg!(&e);
    println!("\nTYPE CHECKING");

    types::Context::default()
        .type_expr(&mut e)
        .map_err(|err| Error::new(ErrorKind::Other, format!("{:?}", err)))?;

    println!("\nEVALUATING");
    eval::Context::default().eval_expr(&e, Lifetime::global());

    Ok(())
}
