use crate::{
    InSource, Instruction, InstructionOperands, JmpCondition, MovDestination, MovOperation,
    MovSource, OutDestination, SetDestination, WaitSource,
};
use alloc::{
    boxed::Box,
    string::{String, ToString},
    vec::Vec,
};
use hashbrown::hash_map::HashMap;

mod pio {
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
    Label(&'input str),
}

#[derive(Debug)]
pub(crate) enum ParsedDirective<'input> {
    SideSet {
        value: Value<'input>,
        opt: bool,
        pindirs: bool,
    },
    WrapTarget,
    Wrap,
    Define {
        name: &'input str,
        value: Value<'input>,
    },
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
            operands: self.operands.refiy(state),
            side_set: match &self.side_set {
                Some(s) => Some(s.reify(state) as u8),
                None => None,
            },
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
    fn refiy(&self, state: &ProgramState) -> InstructionOperands {
        match self {
            ParsedOperands::JMP { condition, address } => InstructionOperands::JMP {
                condition: *condition,
                address: address.reify(state) as u8,
            },
            ParsedOperands::WAIT {
                polarity,
                source,
                index,
            } => InstructionOperands::WAIT {
                polarity: polarity.reify(state) as u8,
                source: *source,
                index: index.reify(state) as u8,
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
    defines: HashMap<String, i32>,
}

#[derive(Debug)]
struct ProgramState<'a> {
    file_state: &'a mut FileState,
    labels: HashMap<String, i32>,
    side_set_size: u8,
    side_set_opt: bool,
    side_set_pindirs: bool,
}

impl<'a> ProgramState<'a> {
    fn resolve(&self, name: &str) -> i32 {
        match self.labels.get(name) {
            Some(v) => *v,
            None => self.file_state.defines[name],
        }
    }
}

#[derive(Debug)]
pub struct Program {
    code: Vec<u16>,
}

type ParseError<'input> = lalrpop_util::ParseError<usize, pio::Token<'input>, &'static str>;

impl Program {
    pub fn parse_file<'input>(source: &'input str) -> Result<Vec<Self>, ParseError<'input>> {
        match pio::FileParser::new().parse(source) {
            Ok(f) => {
                let mut state = FileState::default();
                Ok(f.iter().map(|p| Program::process(p, &mut state)).collect())
            }
            Err(e) => Err(e),
        }
    }

    pub fn parse_program<'input>(source: &'input str) -> Result<Self, ParseError<'input>> {
        match pio::ProgramParser::new().parse(source) {
            Ok(p) => Ok(Program::process(&p, &mut FileState::default())),
            Err(e) => Err(e),
        }
    }

    fn process<'input>(p: &[Line<'input>], file_state: &mut FileState) -> Self {
        let mut state = ProgramState {
            file_state,
            labels: HashMap::new(),
            side_set_size: 0,
            side_set_opt: false,
            side_set_pindirs: false,
        };

        // first pass
        //   - resolve labels
        //   - resolve defines
        //   - read side_set settings
        let mut instr_index = 0;
        for line in p {
            match line {
                Line::Instruction(..) => {
                    instr_index += 1;
                }
                Line::Label(name) => {
                    state.labels.insert(name.to_string(), instr_index as i32);
                }
                Line::Directive(d) => match d {
                    // TODO: support multiple programs using ParsedDirective::Program
                    ParsedDirective::SideSet {
                        value,
                        opt,
                        pindirs,
                    } => {
                        assert!(instr_index == 0);
                        state.side_set_size = value.reify(&state) as u8;
                        state.side_set_opt = *opt;
                        state.side_set_pindirs = *pindirs;
                    }
                    ParsedDirective::Define { name, value } => {
                        state
                            .file_state
                            .defines
                            .insert(name.to_string(), value.reify(&state));
                    }
                    _ => {}
                },
            }
        }

        let mut a = crate::Assembler::new();
        a.set_sideset(state.side_set_opt, state.side_set_size);

        // second pass
        //   - emit instructions
        for line in p {
            if let Line::Instruction(i) = line {
                a.instructions.push(i.reify(&state));
            }
        }

        Program { code: a.assemble() }
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
}

#[test]
fn test_side_set() {
    let p = Program::parse_program(
        "
    .side_set 1 opt

    label:
      pull
      out pins, 1
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
}
