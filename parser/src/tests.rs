use super::*;

macro_rules! test_expected {
    ($input:literal, $output:literal $(,)?) => {
        assert_eq!(format!("{:?}", parse($input).unwrap()), $output);
    };
}

#[test]
fn literals() {
    test_expected!(
        r#"{true false 1 1.5 true "string" ident ["hello","world"]}"#,
        r#"{true, false, 1, 1.5, true, "string", ident, ["hello", "world"]}"#,
    );
    assert_eq!(parse("true"), Ok(Node::from(Literal::Bool(true))));
    assert_eq!(parse("false"), Ok(Node::from(Literal::Bool(false))));
}
#[test]
fn for_loop() {
    test_expected!(r#"for i in expr {"Hello" "World"}"#, r#"for i in expr {"Hello", "World"}"#,);
}
#[test]
fn while_loop() {
    test_expected!(r#"while true {"Hello" "World"}"#, r#"while true {"Hello", "World"}"#);
}
#[test]
fn test_if_statement() {
    test_expected!("if a {}", "if a {}");
    test_expected!(r#"if a {} else if b {} else {"hi"}"#, r#"if a {} else if b {} else {"hi"}"#);
}
#[test]
fn var_decl() {
    test_expected!("let a = 2", "let a = 2");
}
#[test]
fn op_decl() {
    test_expected!("let a += 2", "let a += 2");
    test_expected!("let a -= 2", "let a -= 2");
    test_expected!("let a *= 2", "let a *= 2");
    test_expected!("let a /= 2", "let a /= 2");
    test_expected!("let a %= 2", "let a %= 2");
    test_expected!("let a &&= 2", "let a &&= 2");
    test_expected!("let a ||= 2", "let a ||= 2");
    test_expected!("let a ^= 2", "let a ^= 2");
}
#[test]
fn fn_call() {
    test_expected!("print(1, 2, 3)", "print([1, 2, 3])");
}
#[test]
fn fn_decl() {
    test_expected!("fn hi() {}", "fn hi() {}");
    test_expected!("fn print(s) { print(s) }", "fn print(s) {print([s])}");
}
#[test]
fn single_block() {
    test_expected!(": 1", "{1}");
}

#[test]
fn bin_expr() {
    test_expected!("1 + 1", "(1 + 1)");
    test_expected!("1 + 1 * 1", "(1 + (1 * 1))");
    test_expected!("(1 + 1) * 1", "((1 + 1) * 1)");
    test_expected!("1..2", "(1 .. 2)");
    test_expected!("1..=2", "(1 ..= 2)");
}

mod examples {
    macro_rules! test_example {
        ($name:ident) => {
            #[test]
            fn $name() {
                let name = include_str!(concat!("../../examples/", stringify!($name), ".pty"));
                if let Err(err) = super::parse_many(name) {
                    panic!("{err:#?}");
                }
            }
        };
    }
    test_example!(fizzbuzz);
    test_example!(hello_world);
    test_example!(sum_squares);
    test_example!(while_loop);
}
