// PIO instr grouping is 3/5/3/5
#![allow(clippy::unusual_byte_groupings)]
#![allow(clippy::upper_case_acronyms)]

use pio::{
    InSource, Instruction, InstructionOperands, JmpCondition, MovDestination, MovOperation,
    MovSource, OutDestination, ProgramWithDefines, SetDestination, WaitSource,
};

use std::collections::HashMap;

mod parser {
    #![allow(clippy::all)]
    include!(concat!(env!("OUT_DIR"), "/pio.rs"));
}

#[derive(Debug)]
pub(crate) enum Value<'input> {
    I32(i32),
    Symbol(&'input str),
    Add(Box<Value<'input>>, Box<Value<'input>>),
    Sub(Box<Value<'input>>, Box<Value<'input>>),
    Mul(Box<Value<'input>>, Box<Value<'input>>),
    Div(Box<Value<'input>>, Box<Value<'input>>),
    Neg(Box<Value<'input>>),
    Rev(Box<Value<'input>>),
}

impl<'i> Value<'i> {
    fn reify(&self, state: &ProgramState) -> i32 {
        match self {
            Value::I32(v) => *v,
            Value::Symbol(s) => state.resolve(s),
            Value::Add(a, b) => a.reify(state) + b.reify(state),
            Value::Sub(a, b) => a.reify(state) - b.reify(state),
            Value::Mul(a, b) => a.reify(state) * b.reify(state),
            Value::Div(a, b) => a.reify(state) / b.reify(state),
            Value::Neg(a) => -a.reify(state),
            Value::Rev(a) => a.reify(state).reverse_bits(),
        }
    }
}

#[derive(Debug)]
pub(crate) enum Line<'input> {
    Directive(ParsedDirective<'input>),
    Instruction(ParsedInstruction<'input>),
    Label { public: bool, name: &'input str },
}

#[derive(Debug)]
pub(crate) enum ParsedDirective<'input> {
    Define {
        public: bool,
        name: &'input str,
        value: Value<'input>,
    },
    Origin(Value<'input>),
    SideSet {
        value: Value<'input>,
        opt: bool,
        pindirs: bool,
    },
    WrapTarget,
    Wrap,
    LangOpt(&'input str),
}

#[derive(Debug)]
pub(crate) struct ParsedInstruction<'input> {
    operands: ParsedOperands<'input>,
    side_set: Option<Value<'input>>,
    delay: Value<'input>,
}

impl<'i> ParsedInstruction<'i> {
    fn reify(&self, state: &ProgramState) -> Instruction {
        Instruction {
            operands: self.operands.reify(state),
            side_set: self.side_set.as_ref().map(|s| s.reify(state) as u8),
            delay: self.delay.reify(state) as u8,
        }
    }
}

#[derive(Debug)]
pub(crate) enum ParsedOperands<'input> {
    JMP {
        condition: JmpCondition,
        address: Value<'input>,
    },
    WAIT {
        polarity: Value<'input>,
        source: WaitSource,
        index: Value<'input>,
        relative: bool,
    },
    IN {
        source: InSource,
        bit_count: Value<'input>,
    },
    OUT {
        destination: OutDestination,
        bit_count: Value<'input>,
    },
    PUSH {
        if_full: bool,
        block: bool,
    },
    PULL {
        if_empty: bool,
        block: bool,
    },
    MOV {
        destination: MovDestination,
        op: MovOperation,
        source: MovSource,
    },
    IRQ {
        clear: bool,
        wait: bool,
        index: Value<'input>,
        relative: bool,
    },
    SET {
        destination: SetDestination,
        data: Value<'input>,
    },
}

impl<'i> ParsedOperands<'i> {
    fn reify(&self, state: &ProgramState) -> InstructionOperands {
        match self {
            ParsedOperands::JMP { condition, address } => InstructionOperands::JMP {
                condition: *condition,
                address: address.reify(state) as u8,
            },
            ParsedOperands::WAIT {
                polarity,
                source,
                index,
                relative,
            } => InstructionOperands::WAIT {
                polarity: polarity.reify(state) as u8,
                source: *source,
                index: index.reify(state) as u8,
                relative: *relative,
            },
            ParsedOperands::IN { source, bit_count } => InstructionOperands::IN {
                source: *source,
                bit_count: bit_count.reify(state) as u8,
            },
            ParsedOperands::OUT {
                destination,
                bit_count,
            } => InstructionOperands::OUT {
                destination: *destination,
                bit_count: bit_count.reify(state) as u8,
            },
            ParsedOperands::PUSH { if_full, block } => InstructionOperands::PUSH {
                if_full: *if_full,
                block: *block,
            },
            ParsedOperands::PULL { if_empty, block } => InstructionOperands::PULL {
                if_empty: *if_empty,
                block: *block,
            },
            ParsedOperands::MOV {
                destination,
                op,
                source,
            } => InstructionOperands::MOV {
                destination: *destination,
                op: *op,
                source: *source,
            },
            ParsedOperands::IRQ {
                clear,
                wait,
                index,
                relative,
            } => InstructionOperands::IRQ {
                clear: *clear,
                wait: *wait,
                index: index.reify(state) as u8,
                relative: *relative,
            },
            ParsedOperands::SET { destination, data } => InstructionOperands::SET {
                destination: *destination,
                data: data.reify(state) as u8,
            },
        }
    }
}

#[derive(Debug, Default)]
struct FileState {
    defines: HashMap<String, (bool, i32)>,
}

#[derive(Debug)]
struct ProgramState<'a> {
    file_state: &'a mut FileState,
    defines: HashMap<String, (bool, i32)>,
}

impl<'a> ProgramState<'a> {
    fn new(file_state: &'a mut FileState) -> Self {
        ProgramState {
            file_state,
            defines: HashMap::new(),
        }
    }

    fn resolve(&self, name: &str) -> i32 {
        match self.defines.get(name) {
            Some(v) => v.1,
            None => self.file_state.defines[name].1,
        }
    }

    fn public_defines(&self) -> HashMap<String, i32> {
        let mut p = HashMap::new();
        for (name, (public, value)) in &self.file_state.defines {
            if *public {
                p.insert(name.to_string(), *value);
            }
        }
        for (name, (public, value)) in &self.defines {
            if *public {
                p.insert(name.to_string(), *value);
            }
        }
        p
    }
}

pub type ParseError<'input> = lalrpop_util::ParseError<usize, parser::Token<'input>, &'static str>;

pub struct Parser<const PROGRAM_SIZE: usize>;

impl<const PROGRAM_SIZE: usize> Parser<PROGRAM_SIZE> {
    /// Parse a PIO "file", which contains some number of PIO programs
    /// separated by `.program` directives.
    pub fn parse_file(
        source: &str,
    ) -> Result<HashMap<String, ProgramWithDefines<HashMap<String, i32>, PROGRAM_SIZE>>, ParseError>
    {
        match parser::FileParser::new().parse(source) {
            Ok(f) => {
                let mut state = FileState::default();

                // set up global defines
                let fake_prog_state = ProgramState::new(&mut state);
                for d in f.0 {
                    if let ParsedDirective::Define {
                        public,
                        name,
                        value,
                    } = d.0
                    {
                        fake_prog_state
                            .file_state
                            .defines
                            .insert(name.to_string(), (public, value.reify(&fake_prog_state)));
                    }
                }

                Ok(f.1
                    .iter()
                    .map(|p| {
                        let program_name = p.0.to_string();
                        (program_name, Parser::process(&p.1, &mut state))
                    })
                    .collect())
            }
            Err(e) => Err(e),
        }
    }

    /// Parse a single PIO program, without the `.program` directive.
    pub fn parse_program(
        source: &str,
    ) -> Result<ProgramWithDefines<HashMap<String, i32>, PROGRAM_SIZE>, ParseError> {
        match parser::ProgramParser::new().parse(source) {
            Ok(p) => Ok(Parser::process(&p, &mut FileState::default())),
            Err(e) => Err(e),
        }
    }

    fn process(
        p: &[Line],
        file_state: &mut FileState,
    ) -> ProgramWithDefines<HashMap<String, i32>, PROGRAM_SIZE> {
        let mut state = ProgramState::new(file_state);

        // first pass
        //   - resolve labels
        //   - resolve defines
        //   - read side set settings
        let mut side_set_size = 0;
        let mut side_set_opt = false;
        let mut side_set_pindirs = false;
        let mut origin = None;
        let mut wrap_target = None;
        let mut wrap = None;
        let mut instr_index = 0;
        for line in p {
            match line {
                Line::Instruction(..) => {
                    instr_index += 1;
                }
                Line::Label { public, name } => {
                    state
                        .defines
                        .insert(name.to_string(), (*public, instr_index as i32));
                }
                Line::Directive(d) => match d {
                    ParsedDirective::Define {
                        public,
                        name,
                        value,
                    } => {
                        state
                            .defines
                            .insert(name.to_string(), (*public, value.reify(&state)));
                    }
                    ParsedDirective::Origin(value) => {
                        origin = Some(value.reify(&state) as u8);
                    }
                    ParsedDirective::SideSet {
                        value,
                        opt,
                        pindirs,
                    } => {
                        assert!(instr_index == 0);
                        side_set_size = value.reify(&state) as u8;
                        side_set_opt = *opt;
                        side_set_pindirs = *pindirs;
                    }
                    ParsedDirective::WrapTarget => {
                        assert!(wrap_target.is_none());
                        wrap_target = Some(instr_index);
                    }
                    ParsedDirective::Wrap => {
                        assert!(wrap.is_none());
                        wrap = Some(instr_index - 1);
                    }
                    _ => {}
                },
            }
        }

        let mut a = pio::Assembler::new_with_side_set(pio::SideSet::new(
            side_set_opt,
            side_set_size,
            side_set_pindirs,
        ));

        // second pass
        //   - emit instructions
        for line in p {
            if let Line::Instruction(i) = line {
                a.instructions.push(i.reify(&state));
            }
        }

        let program = a.assemble_program().set_origin(origin);

        let program = match (wrap, wrap_target) {
            (Some(wrap_source), Some(wrap_target)) => program.set_wrap(pio::Wrap {
                source: wrap_source,
                target: wrap_target,
            }),
            (None, None) => program,
            _ => panic!(
                "must define either both or neither of wrap and wrap_target, but not only one of them"
            ),
        };

        ProgramWithDefines {
            program,
            public_defines: state.public_defines(),
        }
    }
}

#[test]
fn test() {
    let p = Program::parse_program(
        "
    label:
      pull
      out pins, 1
      jmp label
    ",
    )
    .unwrap();

    assert_eq!(
        p.code,
        &[
            // LABEL:
            0b100_00000_101_00000, // PULL
            0b011_00000_000_00001, // OUT PINS, 1
            0b000_00000_000_00000, // JMP LABEL
        ]
    );
    assert_eq!(p.origin, None);
    assert_eq!(p.wrap, (0, 2));
}

#[test]
fn test_side_set() {
    let p = Program::parse_program(
        "
    .side_set 1 opt
    .origin 5

    label:
      pull
      .wrap_target
      out pins, 1
      .wrap
      jmp label side 1
    ",
    )
    .unwrap();

    assert_eq!(
        p.code,
        &[
            // LABEL:
            0b100_00000_101_00000, // PULL
            0b011_00000_000_00001, // OUT PINS, 1
            0b000_11000_000_00000, // JMP LABEL, SIDE 1
        ]
    );
    assert_eq!(p.origin, Some(5));
    assert_eq!(p.wrap, (1, 1));
}
