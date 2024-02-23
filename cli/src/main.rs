use parser::parse_many;

fn main() {
    let input = include_str!("../../examples/fizzbuzz.pty");
    let ast = parse_many(input).unwrap();
    println!("{ast:#?}");
}
