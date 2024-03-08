macro_rules! load_test {
    ($name:ident) => {
        #[test]
        fn $name() {
            let input = include_str!("if_statement.pty");
            let input = input.replace("\r\n", "\n");

            let repr = parser::parse_many(&input).unwrap();
            let output = super::format_many(&repr, super::Config::default());
            assert_eq!(input, output);
        }
    };
}

load_test!(if_statement);
