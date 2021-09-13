extern crate proc_macro;
use lalrpop_util::ParseError;
use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;

/// Maximum program size supported by the macro.
///
/// As the program size is limited to 32 instructions on the currently available hardware as of 2021, 1024 instructions
/// should be plenty for a while.
const MAX_PROGRAM_SIZE: usize = 1024;

struct PioMacroArgs {
    program_size: syn::Expr,
    _comma: syn::token::Comma,
    source: syn::LitStr,
}

impl syn::parse::Parse for PioMacroArgs {
    fn parse(stream: syn::parse::ParseStream) -> syn::parse::Result<Self> {
        Ok(Self {
            program_size: stream.parse()?,
            _comma: stream.parse()?,
            source: stream.parse()?,
        })
    }
}

/// A macro which invokes the PIO assembler at compile time.
#[proc_macro]
pub fn pio(item: TokenStream) -> TokenStream {
    let args = parse_macro_input!(item as PioMacroArgs);
    let result =
        match pio_parser::Parser::<{ MAX_PROGRAM_SIZE }>::parse_program(&args.source.value()) {
            Ok(pio_parser::Program {
                program,
                public_defines,
            }) => {
                let origin: proc_macro2::TokenStream =
                    format!("{:?}", program.origin).parse().unwrap();
                let code: proc_macro2::TokenStream = format!(
                    "::std::iter::IntoIterator::into_iter([{}]).collect()",
                    program
                        .code
                        .iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<String>>()
                        .join(",")
                )
                .parse()
                .unwrap();
                let wrap: proc_macro2::TokenStream = format!(
                    "::pio::Wrap {{source: {}, target: {}}}",
                    program.wrap.source, program.wrap.target
                )
                .parse()
                .unwrap();
                let side_set: proc_macro2::TokenStream = format!(
                    "::pio::SideSet::new_from_proc_macro({}, {}, {})",
                    program.side_set.optional(),
                    program.side_set.bits(),
                    program.side_set.pindirs()
                )
                .parse()
                .unwrap();
                let defines_struct: proc_macro2::TokenStream = format!(
                    "
            struct ExpandedDefines {{
                {}
            }}
            ",
                    public_defines
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
                    public_defines
                        .iter()
                        .map(|(k, v)| format!("{}: {},", k, v))
                        .collect::<Vec<String>>()
                        .join("\n")
                )
                .parse()
                .unwrap();
                let program_size = args.program_size;
                quote! {
                    {
                        #defines_struct
                        ::pio_parser::Program {
                            program: ::pio::Program::<{ #program_size }> {
                                code: #code,
                                origin: #origin,
                                wrap: #wrap,
                                side_set: #side_set,
                            },
                            public_defines: #defines_init,
                        }
                    }
                }
            }
            Err(e) => {
                let files =
                    codespan_reporting::files::SimpleFile::new("source", args.source.value());

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
