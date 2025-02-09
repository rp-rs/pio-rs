use lalrpop_util::ParseError;
use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_error2::{abort, abort_call_site, proc_macro_error};
use quote::quote;
use std::collections::HashMap;
use std::fmt::Write;
use std::fs;
use std::path::{Path, PathBuf};
use syn::{
    parenthesized, parse, parse_macro_input, Expr, ExprLit, Ident, Lit, LitInt, LitStr, Token,
};

/// Maximum program size supported by the macro.
///
/// As the program size is limited to 32 instructions on the currently available hardware as of 2021, 1024 instructions
/// should be plenty for a while.
const MAX_PROGRAM_SIZE: usize = 1024;

struct OptionsArgs {
    ident: Ident,
    expr: Expr,
}

impl syn::parse::Parse for OptionsArgs {
    fn parse(stream: syn::parse::ParseStream) -> syn::parse::Result<Self> {
        let ident = stream.parse()?;
        let _equals: Token![=] = stream.parse()?;
        let expr = stream.parse()?;

        Ok(Self { ident, expr })
    }
}

// Options are on the form Ident = Literal
struct Options {
    options: HashMap<String, (Ident, Expr)>,
}

impl Options {
    fn validate(&self) -> Result<(), parse::Error> {
        // NOTE: Add more options here in the future
        let valid_identifiers = ["max_program_size"];

        for (name, (id, _)) in &self.options {
            if !valid_identifiers.contains(&name.as_str()) {
                abort!(
                    id,
                    "unknown identifier, expected one of {:?}",
                    valid_identifiers
                );
            }
        }

        Ok(())
    }

    fn get_max_program_size_or_default(&self) -> Result<Expr, parse::Error> {
        if let Some(mps) = self.options.get("max_program_size") {
            Ok(mps.1.clone())
        } else {
            Ok(Expr::Lit(ExprLit {
                attrs: vec![],
                lit: Lit::Int(LitInt::new("32", Span::call_site())),
            }))
        }
    }
}

impl syn::parse::Parse for Options {
    fn parse(stream: syn::parse::ParseStream) -> parse::Result<Self> {
        // Parse the optional 'options'
        let content;
        parenthesized!(content in stream);

        if !content.is_empty() {
            let mut options = HashMap::new();

            while !content.is_empty() {
                let opt: OptionsArgs = content.parse()?;
                options.insert(opt.ident.to_string(), (opt.ident, opt.expr));
                let _trailing_comma: Option<Token![,]> = content.parse().ok();
            }

            let _trailing_comma: Option<Token![,]> = stream.parse().ok();

            let s = Self { options };

            s.validate()?;

            Ok(s)
        } else {
            Ok(Self {
                options: HashMap::new(),
            })
        }
    }
}

struct SelectProgram {
    name: String,
    ident: LitStr,
}

impl syn::parse::Parse for SelectProgram {
    fn parse(stream: syn::parse::ParseStream) -> parse::Result<Self> {
        // Parse the optional 'options'
        let content;
        parenthesized!(content in stream);

        let name: LitStr = content.parse::<LitStr>()?;

        Ok(Self {
            name: name.value(),
            ident: name,
        })
    }
}

struct PioFileMacroArgs {
    krate: Ident,
    max_program_size: Expr,
    program: String,
    program_name: Option<(String, LitStr)>,
    file_path: PathBuf,
}

impl syn::parse::Parse for PioFileMacroArgs {
    fn parse(stream: syn::parse::ParseStream) -> syn::parse::Result<Self> {
        let krate: Ident = stream.parse()?;
        let _comma: Option<Token![,]> = stream.parse()?;

        let mut program = String::new();
        let mut file_path = PathBuf::new();

        // Parse the list of instructions
        if let Ok(s) = stream.parse::<LitStr>() {
            let path = s.value();
            let path = Path::new(&path);

            let pathbuf = {
                let mut p = PathBuf::new();

                if path.is_relative() {
                    if let Some(crate_dir) = std::env::var_os("CARGO_MANIFEST_DIR") {
                        p.push(crate_dir);
                    } else {
                        abort!(s, "Cannot find 'CARGO_MANIFEST_DIR' environment variable");
                    }
                }

                p.push(path);

                p
            };

            if !pathbuf.exists() {
                abort!(s, "the file '{}' does not exist", pathbuf.display());
            }

            file_path = pathbuf.to_owned();

            match fs::read(pathbuf) {
                Ok(content) => match std::str::from_utf8(&content) {
                    Ok(prog) => program = prog.to_string(),
                    Err(e) => {
                        abort!(s, "could parse file: '{}'", e);
                    }
                },
                Err(e) => {
                    abort!(s, "could not read file: '{}'", e);
                }
            }

            let _trailing_comma: Option<Token![,]> = stream.parse().ok();
        }

        let mut select_program = None;
        let mut options = Options {
            options: HashMap::new(),
        };

        for _ in 0..2 {
            if let Ok(ident) = stream.parse::<Ident>() {
                match ident.to_string().as_str() {
                    "select_program" => {
                        // Parse the optional 'select_program'
                        let sp: SelectProgram = stream.parse()?;
                        select_program = Some(sp);
                        let _trailing_comma: Option<Token![,]> = stream.parse().ok();
                    }
                    "options" => {
                        // Parse the optional 'options'
                        let opt: Options = stream.parse()?;
                        options = opt;
                        let _trailing_comma: Option<Token![,]> = stream.parse().ok();
                    }
                    _ => abort!(ident, "expected one of 'options' or 'select_program'"),
                }
            }
        }

        if !stream.is_empty() {
            abort!(stream.span(), "expected end of input");
        }

        // Validate options
        let max_program_size = options.get_max_program_size_or_default()?;

        Ok(Self {
            krate,
            program_name: select_program.map(|v| (v.name, v.ident)),
            max_program_size,
            program,
            file_path,
        })
    }
}

struct PioAsmMacroArgs {
    krate: Ident,
    max_program_size: Expr,
    program: String,
}

impl syn::parse::Parse for PioAsmMacroArgs {
    fn parse(stream: syn::parse::ParseStream) -> syn::parse::Result<Self> {
        let krate: Ident = stream.parse()?;
        let _comma: Option<Token![,]> = stream.parse()?;

        let mut program = String::new();

        // Parse the list of instructions
        while let Ok(s) = stream.parse::<LitStr>() {
            writeln!(&mut program, "{}", s.value()).unwrap();

            let _trailing_comma: Option<Token![,]> = stream.parse().ok();
        }

        // Parse the optional 'options'

        let mut options = Options {
            options: HashMap::new(),
        };

        if let Ok(ident) = stream.parse::<Ident>() {
            if ident == "options" {
                let opt: Options = stream.parse()?;
                options = opt;
                let _trailing_comma: Option<Token![,]> = stream.parse().ok();
            }
        }

        if !stream.is_empty() {
            abort!(stream.span(), "expected end of input");
        }

        // Validate options
        let max_program_size = options.get_max_program_size_or_default()?;

        Ok(Self {
            krate,
            max_program_size,
            program,
        })
    }
}

#[proc_macro]
#[proc_macro_error]
pub fn pio_file_inner(item: TokenStream) -> TokenStream {
    let args = parse_macro_input!(item as PioFileMacroArgs);
    let parsed_programs = pio_parser::Parser::<{ MAX_PROGRAM_SIZE }>::parse_file(&args.program);
    let program = match &parsed_programs {
        Ok(programs) => {
            if let Some((program_name, ident)) = args.program_name {
                if let Some(program) = programs.get(&program_name) {
                    program
                } else {
                    abort! { ident, "program name not found in the provided file" }
                }
            } else {
                // No name provided, check if there is only one in the map

                match programs.len() {
                    0 => abort_call_site! { "no programs in the provided file" },
                    1 => programs.iter().next().unwrap().1,
                    _ => {
                        abort_call_site! { "more than 1 program in the provided file, select one using `select_program(\"my_program\")`" }
                    }
                }
            }
        }
        Err(e) => return parse_error(e, &args.program).into(),
    };

    to_codegen(
        args.krate,
        program,
        args.max_program_size,
        Some(
            args.file_path
                .into_os_string()
                .into_string()
                .expect("file path must be valid UTF-8"),
        ),
    )
    .into()
}

/// A macro which invokes the PIO assembler at compile time.
#[proc_macro]
#[proc_macro_error]
pub fn pio_asm_inner(item: TokenStream) -> TokenStream {
    let args = parse_macro_input!(item as PioAsmMacroArgs);

    let parsed_program = pio_parser::Parser::<{ MAX_PROGRAM_SIZE }>::parse_program(&args.program);

    let program = match &parsed_program {
        Ok(program) => program,
        Err(e) => return parse_error(e, &args.program).into(),
    };

    to_codegen(args.krate, program, args.max_program_size, None).into()
}

fn to_codegen(
    krate: Ident,
    program: &pio_core::ProgramWithDefines<HashMap<String, i32>, { MAX_PROGRAM_SIZE }>,
    max_program_size: Expr,
    file: Option<String>,
) -> proc_macro2::TokenStream {
    let pio_core::ProgramWithDefines {
        program,
        public_defines,
    } = program;
    if let Expr::Lit(ExprLit {
        attrs: _,
        lit: Lit::Int(i),
    }) = &max_program_size
    {
        if let Ok(mps) = i.base10_parse::<usize>() {
            if program.code.len() > mps {
                abort_call_site!(
                    "the resulting program is larger than the maximum allowed: max = {}, size = {}",
                    mps,
                    program.code.len()
                );
            }
        }
    }

    let origin = if let Some(origin) = program.origin {
        quote!(Some(#origin))
    } else {
        quote!(None)
    };

    let code = &program.code;
    let code = quote!(
        ::core::iter::IntoIterator::into_iter([#(#code),*]).collect()
    );

    let wrap_source = program.wrap.source;
    let wrap_target = program.wrap.target;
    let wrap = quote!(
        #krate::Wrap {source: #wrap_source, target: #wrap_target}
    );

    let side_set_optional = program.side_set.optional();
    let side_set_bits = program.side_set.bits();
    let side_set_pindirs = program.side_set.pindirs();
    let side_set = quote!(
        #krate::SideSet::new_from_proc_macro(
            #side_set_optional,
            #side_set_bits,
            #side_set_pindirs,
        )
    );

    let version = Ident::new(&format!("{:?}", program.version), Span::call_site());
    let version = quote!(#krate::PioVersion::#version);

    let defines_fields = public_defines
        .keys()
        .map(|k| Ident::new(k, Span::call_site()))
        .collect::<Vec<_>>();
    let defines_values = public_defines.values();
    let defines_struct = quote!(
        struct ExpandedDefines {
            #(#defines_fields: i32,)*
        }
    );
    let defines_init = quote!(
        ExpandedDefines {
            #(#defines_fields: #defines_values,)*
        }
    );

    let program_size = max_program_size;

    // This makes sure the file is added to the list
    // of tracked files, so a change of that file triggers
    // a recompile. Should be replaced by
    // `proc_macro::tracked_path::path` when it is stable.
    let dummy_include = match file {
        Some(file_path) => quote! {let _ = include_bytes!( #file_path );},
        None => quote!(),
    };
    quote! {
        {
            #defines_struct
            {
                #dummy_include;
                #krate::ProgramWithDefines {
                    program: #krate::Program::<{ #program_size }> {
                        code: #code,
                        origin: #origin,
                        wrap: #wrap,
                        side_set: #side_set,
                        version: #version,
                    },
                    public_defines: #defines_init,
                }
            }
        }
    }
}

fn parse_error(error: &pio_parser::ParseError, program_source: &str) -> proc_macro2::TokenStream {
    let e = error;
    let files = codespan_reporting::files::SimpleFile::new("source", program_source);

    let (loc, messages) = match e {
        ParseError::InvalidToken { location } => {
            (*location..*location, vec!["invalid token".to_string()])
        }
        ParseError::UnrecognizedEof { location, expected } => (
            *location..*location,
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
