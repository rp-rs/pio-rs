extern crate proc_macro;
use lalrpop_util::ParseError;
use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;

/// A macro which invokes the PIO assembler at compile time.
#[proc_macro]
pub fn pio(item: TokenStream) -> TokenStream {
    let source = parse_macro_input!(item as syn::LitStr);
    let result = match pio::parser::Program::parse_program(&source.value()) {
        Ok(p) => {
            let origin: proc_macro2::TokenStream = format!("{:?}", p.origin()).parse().unwrap();
            let code: proc_macro2::TokenStream = format!(
                "::pio::alloc::vec![{}]",
                p.code()
                    .iter()
                    .map(|v| v.to_string())
                    .collect::<Vec<String>>()
                    .join(",")
            )
            .parse()
            .unwrap();
            let wrap: proc_macro2::TokenStream =
                format!("({}, {})", p.wrap().0, p.wrap().1).parse().unwrap();
            let defines_struct: proc_macro2::TokenStream = format!(
                "
            struct ExpandedDefines {{
                {}
            }}
            ",
                p.public_defines()
                    .keys()
                    .map(|k| format!("{}: i32,", k))
                    .collect::<Vec<String>>()
                    .join("\n")
            )
            .parse()
            .unwrap();
            let defines_init: proc_macro2::TokenStream = format!(
                "
            ExpandedDefines {{
                {}
            }}
            ",
                p.public_defines()
                    .iter()
                    .map(|(k, v)| format!("{}: {},", k, v))
                    .collect::<Vec<String>>()
                    .join("\n")
            )
            .parse()
            .unwrap();
            quote! {
                {
                    #defines_struct
                    pio::parser::Program::new_from_proc_macro(
                        #origin, #code, #wrap, #defines_init,
                    )
                }
            }
        }
        Err(e) => {
            let files = codespan_reporting::files::SimpleFile::new("source", source.value());

            let (loc, messages) = match e {
                ParseError::InvalidToken { location } => {
                    (location..location, vec!["invalid token".to_string()])
                }
                ParseError::UnrecognizedEOF { location, expected } => (
                    location..location,
                    vec![
                        "unrecognized eof".to_string(),
                        format!("expected one of {}", expected.join(", ")),
                    ],
                ),
                ParseError::UnrecognizedToken { token, expected } => (
                    token.0..token.2,
                    vec![
                        format!("unexpected token: {:?}", format!("{}", token.1)),
                        format!("expected one of {}", expected.join(", ")),
                    ],
                ),
                ParseError::ExtraToken { token } => {
                    (token.0..token.2, vec![format!("extra token: {}", token.1)])
                }
                ParseError::User { error } => (0..0, vec![error.to_string()]),
            };

            let diagnostic = codespan_reporting::diagnostic::Diagnostic::error()
                .with_message(messages[0].clone())
                .with_labels(
                    messages
                        .iter()
                        .enumerate()
                        .map(|(i, m)| {
                            codespan_reporting::diagnostic::Label::new(
                                if i == 0 {
                                    codespan_reporting::diagnostic::LabelStyle::Primary
                                } else {
                                    codespan_reporting::diagnostic::LabelStyle::Secondary
                                },
                                (),
                                loc.clone(),
                            )
                            .with_message(m)
                        })
                        .collect(),
                );

            let mut writer = codespan_reporting::term::termcolor::Buffer::ansi();
            let config = codespan_reporting::term::Config::default();
            codespan_reporting::term::emit(&mut writer, &config, &files, &diagnostic).unwrap();
            let data = writer.into_inner();
            let data = std::str::from_utf8(&data).unwrap();

            quote! {
                compile_error!(#data)
            }
        }
    };
    TokenStream::from(result)
}
