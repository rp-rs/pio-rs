//! PIO
//!
//! ```rust
//! // Repeatedly get one word of data from the TX FIFO, stalling when
//! // the FIFO is empty. Write the least significant bit to the OUT pin
//! // group.
//! // https://github.com/raspberrypi/pico-examples/tree/master/pio/hello_pio/hello.pio
//! let mut a = pio::Assembler::new();
//!
//! let mut loop_label = a.label();
//!
//! a.bind(&mut loop_label);
//! a.pull(false, false);
//! a.out(pio::OutDestination::PINS, 1);
//! a.jmp(pio::JmpCondition::Always, &mut loop_label);
//!
//! let program = a.assemble();
//! ```

// PIO instr grouping is 3/5/3/5
#![allow(clippy::unusual_byte_groupings)]

pub mod parser;

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum JmpCondition {
    /// Always
    Always = 0b000,
    /// `!X`: scratch X zero
    XIsZero = 0b001,
    /// `X--`: scratch X non-zero, post decrement
    XDecNonZero = 0b010,
    /// `!Y`: scratch Y zero
    YIsZero = 0b011,
    /// `Y--`: scratch Y non-zero, post decrement
    YDecNonZero = 0b100,
    /// `X!=Y`: scratch X not equal to scratch Y
    XNotEqualY = 0b101,
    /// `PIN`: branch on input pin
    PinHigh = 0b110,
    /// `!OSRE`: output shift register not empty
    OutputShiftRegisterNotEmpty = 0b111,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum WaitSource {
    GPIO = 0b00,
    PIN = 0b01,
    IRQ = 0b10,
    // RESERVED = 0b11,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum InSource {
    PINS = 0b000,
    X = 0b001,
    Y = 0b010,
    NULL = 0b011,
    // RESERVED = 0b100,
    // RESERVED = 0b101,
    ISR = 0b110,
    OSR = 0b111,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum OutDestination {
    PINS = 0b000,
    X = 0b001,
    Y = 0b010,
    NULL = 0b011,
    PINDIRS = 0b100,
    PC = 0b101,
    ISR = 0b110,
    EXEC = 0b111,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum MovDestination {
    PINS = 0b000,
    X = 0b001,
    Y = 0b010,
    // RESERVED = 0b011,
    EXEC = 0b100,
    PC = 0b101,
    ISR = 0b110,
    OSR = 0b111,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum MovOperation {
    None = 0b00,
    Invert = 0b01,
    BitReverse = 0b10,
    // Reserved = 0b11,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum MovSource {
    PINS = 0b000,
    X = 0b001,
    Y = 0b010,
    NULL = 0b011,
    // RESERVED = 0b100,
    STATUS = 0b101,
    ISR = 0b110,
    OSR = 0b111,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum SetDestination {
    PINS = 0b000,
    X = 0b001,
    Y = 0b010,
    // RESERVED = 0b011,
    PINDIRS = 0b100,
    // RESERVED = 0b101,
    // RESERVED = 0b110,
    // RESERVED = 0b111,
}

#[derive(Debug)]
enum InstructionOperands {
    JMP {
        condition: JmpCondition,
        address: u8,
    },
    WAIT {
        /// 1 -> wait for 1
        /// 0 -> wait for 0
        polarity: u8,
        source: WaitSource,
        index: u8,
    },
    IN {
        source: InSource,
        bit_count: u8,
    },
    OUT {
        destination: OutDestination,
        bit_count: u8,
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
        index: u8,
    },
    SET {
        destination: SetDestination,
        data: u8,
    },
}

impl InstructionOperands {
    fn discrim(&self) -> u16 {
        match self {
            InstructionOperands::JMP { .. } => 0b000,
            InstructionOperands::WAIT { .. } => 0b001,
            InstructionOperands::IN { .. } => 0b010,
            InstructionOperands::OUT { .. } => 0b011,
            InstructionOperands::PUSH { .. } => 0b100,
            InstructionOperands::PULL { .. } => 0b100,
            InstructionOperands::MOV { .. } => 0b101,
            InstructionOperands::IRQ { .. } => 0b110,
            InstructionOperands::SET { .. } => 0b111,
        }
    }

    fn operands(&self) -> (u8, u8) {
        match self {
            InstructionOperands::JMP { condition, address } => (*condition as u8, *address),
            InstructionOperands::WAIT {
                polarity,
                source,
                index,
            } => (polarity << 2 | (*source as u8), *index),
            InstructionOperands::IN { source, bit_count } => (*source as u8, *bit_count),
            InstructionOperands::OUT {
                destination,
                bit_count,
            } => (*destination as u8, *bit_count),
            InstructionOperands::PUSH { if_full, block } => {
                ((*if_full as u8) << 1 | (*block as u8), 0)
            }
            InstructionOperands::PULL { if_empty, block } => {
                (1 << 2 | (*if_empty as u8) << 1 | (*block as u8), 0)
            }
            InstructionOperands::MOV {
                destination,
                op,
                source,
            } => (*destination as u8, (*op as u8) << 3 | (*source as u8)),
            InstructionOperands::IRQ { clear, wait, index } => {
                ((*clear as u8) << 1 | (*wait as u8), *index)
            }
            InstructionOperands::SET { destination, data } => (*destination as u8, *data),
        }
    }

    fn encode(&self) -> u16 {
        let mut data: u16 = 0;
        data |= self.discrim() << 13;
        let (o0, o1) = self.operands();
        data |= (o0 as u16) << 5;
        data |= o1 as u16;
        data
    }
}

#[derive(Debug)]
pub(crate) struct Instruction {
    operands: InstructionOperands,
    delay: u8,
    side_set: Option<u8>,
}

impl Instruction {
    fn encode(&self, a: &Assembler) -> u16 {
        let mut data = self.operands.encode();

        if self.delay > a.delay_max {
            panic!("delay limit is {}", a.delay_max);
        }

        let side_set = if let Some(s) = self.side_set {
            if s > a.side_set_max {
                panic!("'side' set must be >=0 and <={}", a.side_set_max);
            }
            let s = (s as u16) << (5 - a.side_set_bits);
            if a.side_set_opt {
                s | 0b10000
            } else {
                s
            }
        } else if a.side_set_bits > 0 && !a.side_set_opt {
            panic!("instruction requires 'side' set");
        } else {
            0
        };

        data |= ((self.delay as u16) | side_set) << 8;

        data
    }
}

#[derive(Debug)]
enum LabelState {
    Unbound(u8),
    Bound(u8),
}

/// A label.
#[derive(Debug)]
pub struct Label {
    state: LabelState,
}

impl Drop for Label {
    fn drop(&mut self) {
        if let LabelState::Unbound(_) = self.state {
            panic!("label was not bound");
        }
    }
}

/// A PIO Assembler. See chapter three of the [RP2040 Datasheet][].
///
/// [RP2040 Datasheet]: https://rptl.io/pico-datasheet
pub struct Assembler {
    instructions: Vec<Instruction>,
    side_set_opt: bool,
    side_set_max: u8,
    side_set_bits: u8,
    delay_max: u8,
}

impl Assembler {
    /// Create a new Assembler.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Assembler {
        Assembler {
            instructions: Vec::new(),
            side_set_opt: false,
            side_set_max: 0,
            side_set_bits: 0,
            delay_max: 31,
        }
    }

    pub fn set_sideset(&mut self, opt: bool, mut bits: u8) {
        self.side_set_opt = opt;
        self.side_set_max = (1 << bits) - 1;
        if opt {
            bits += 1;
        }
        self.side_set_bits = bits;
        self.delay_max = (1 << (5 - self.side_set_bits)) - 1;
    }

    /// Assemble the program into PIO instructions.
    pub fn assemble(self) -> Vec<u16> {
        self.instructions.iter().map(|i| i.encode(&self)).collect()
    }
}

impl Assembler {
    /// Create a new unbound Label.
    pub fn label(&mut self) -> Label {
        Label {
            state: LabelState::Unbound(std::u8::MAX),
        }
    }

    /// Bind `label` to the current instruction position.
    pub fn bind(&mut self, label: &mut Label) {
        match label.state {
            LabelState::Bound(_) => panic!("cannot bind label twice"),
            LabelState::Unbound(mut patch) => {
                let resolved_address = self.instructions.len() as u8;
                while patch != std::u8::MAX {
                    // SAFETY: patch points to the next instruction to patch
                    let instr = unsafe { self.instructions.get_unchecked_mut(patch as usize) };
                    if let InstructionOperands::JMP { address, .. } = &mut instr.operands {
                        patch = *address;
                        *address = resolved_address;
                    } else {
                        unreachable!();
                    }
                }
                label.state = LabelState::Bound(resolved_address);
            }
        }
    }
}

macro_rules! instr_impl {
    ( $(#[$inner:ident $($args:tt)*])* $name:ident ( $self:ident, $( $arg_name:ident : $arg_ty:ty ),* ) $body:expr, $delay:expr, $side_set:expr ) => {
        $(#[$inner $($args)*])*
        pub fn $name(
            &mut $self,
            $( $arg_name : $arg_ty , )*
        ) {
            $self.instructions.push(Instruction {
                operands: $body,
                delay: $delay,
                side_set: $side_set,
            })
        }
    }
}

macro_rules! instr {
    ( $(#[$inner:ident $($args:tt)*])* $name:ident ( $self:ident, $( $arg_name:ident : $arg_ty:ty ),* ) $body:expr ) => {
        instr_impl!($(#[$inner $($args)*])* $name ( $self, $( $arg_name: $arg_ty ),* ) $body, 0, None );
        paste::paste! {
            instr_impl!($(#[$inner $($args)*])* [< $name _with_delay >] ( $self, $( $arg_name: $arg_ty ),* , delay: u8 ) $body, delay, None );
            instr_impl!($(#[$inner $($args)*])* [< $name _with_side_set >] ( $self, $( $arg_name: $arg_ty ),* , side_set: u8 ) $body, 0, Some(side_set) );
            instr_impl!($(#[$inner $($args)*])* [< $name _with_delay_and_side_set >] ( $self, $( $arg_name: $arg_ty ),* , delay: u8, side_set: u8 ) $body, delay, Some(side_set) );
        }
    }
}

impl Assembler {
    instr!(
        /// Emit a `jmp` instruction to `label` for `condition`.
        jmp(self, condition: JmpCondition, label: &mut Label) {
        let address = match label.state {
            LabelState::Unbound(a) => {
                label.state = LabelState::Unbound(self.instructions.len() as u8);
                a
            }
            LabelState::Bound(a) => a,
        };
        InstructionOperands::JMP {
            condition,
            address,
        }
    });

    instr!(
        /// Emit a `wait` instruction with `polarity` from `source` with `index`.
        wait(self, polarity: u8, source: WaitSource, index: u8) {
            InstructionOperands::WAIT {
                polarity,
                source,
                index,
            }
        }
    );

    instr!(
        /// Emit an `in` instruction from `source` with `bit_count`.
        r#in(self, source: InSource, bit_count: u8) {
            InstructionOperands::IN { source, bit_count }
        }
    );

    instr!(
        /// Emit an `out` instruction to `source` with `bit_count`.
        out(self, destination: OutDestination, bit_count: u8) {
            InstructionOperands::OUT {
                destination,
                bit_count,
            }
        }
    );

    instr!(
        /// Emit a `push` instruction with `if_full` and `block`.
        push(self, if_full: bool, block: bool) {
            InstructionOperands::PUSH {
                if_full,
                block,
            }
        }
    );

    instr!(
        /// Emit a `pull` instruction with `if_empty` and `block`.
        pull(self, if_empty: bool, block: bool) {
            InstructionOperands::PULL {
                if_empty,
                block,
            }
        }
    );

    instr!(
        /// Emit a `mov` instruction to `destination` using `op` from `source`.
        mov(self, destination: MovDestination, op: MovOperation, source: MovSource) {
            InstructionOperands::MOV {
                destination,
                op,
                source,
            }
        }
    );

    instr!(
        /// Emit an `irq` instruction using `clear` and `wait` with `index`.
        irq(self, clear: bool, wait: bool, index: u8) {
            InstructionOperands::IRQ {
                clear,
                wait,
                index,
            }
        }
    );

    instr!(
        /// Emit a `set` instruction
        set(self, destination: SetDestination, data: u8) {
            InstructionOperands::SET {
                destination,
                data,
            }
        }
    );
}

#[test]
fn test_jump_1() {
    let mut a = Assembler::new();

    let mut l = a.label();
    a.set(SetDestination::X, 0);
    a.bind(&mut l);
    a.set(SetDestination::X, 1);
    a.jmp(JmpCondition::Always, &mut l);

    assert_eq!(
        a.assemble(),
        &[
            0b111_00000_001_00000, // SET X 0
            // L:
            0b111_00000_001_00001, // SET X 1
            0b000_00000_000_00001, // JMP L
        ]
    );
}

#[test]
fn test_jump_2() {
    let mut a = Assembler::new();

    let mut top = a.label();
    let mut bottom = a.label();
    a.bind(&mut top);
    a.set(SetDestination::Y, 0);
    a.jmp(JmpCondition::YIsZero, &mut bottom);
    a.jmp(JmpCondition::Always, &mut top);
    a.bind(&mut bottom);
    a.set(SetDestination::Y, 1);

    assert_eq!(
        a.assemble(),
        &[
            // TOP:
            0b111_00000_010_00000, // SET Y 0
            0b000_00000_011_00011, // JMP YIsZero BOTTOM
            0b000_00000_000_00000, // JMP Always TOP
            // BOTTOM:
            0b111_00000_010_00001, // SET Y 1
        ]
    );
}

macro_rules! instr_test {
    ($name:ident ( $( $v:expr ),* ) , $b:expr, $a_name:ident, $init:expr) => {
        paste::paste! {
            #[test]
            fn [< test _ $name _ $b >]() {
                let mut $a_name = Assembler::new();
                $init;
                $a_name.$name(
                    $( $v ),*
                );
                let a = $a_name.assemble()[0];
                let b = $b;
                if a != b {
                    panic!("assertion failure: (left == right)\nleft:  {:#016b}\nright: {:#016b}", a, b);
                }
            }
        }
    };

    ($name:ident ( $( $v:expr ),* ) , $b:expr) => {
        instr_test!( $name ( $( $v ),* ), $b, a, {} );
    };
}

instr_test!(wait(0, WaitSource::IRQ, 10), 0b001_00000_010_01010);
instr_test!(wait(1, WaitSource::IRQ, 15), 0b001_00000_110_01111);
instr_test!(
    wait_with_delay(0, WaitSource::IRQ, 10, 30),
    0b001_11110_010_01010
);
instr_test!(
    wait_with_side_set(0, WaitSource::IRQ, 10, 0b10101),
    0b001_10101_010_01010,
    a,
    {
        a.set_sideset(false, 5);
    }
);

instr_test!(r#in(InSource::Y, 10), 0b010_00000_010_01010);

instr_test!(out(OutDestination::Y, 10), 0b011_00000_010_01010);

instr_test!(push(true, false), 0b100_00000_010_00000);
instr_test!(push(false, true), 0b100_00000_001_00000);

instr_test!(pull(true, false), 0b100_00000_110_00000);
instr_test!(pull(false, true), 0b100_00000_101_00000);

instr_test!(
    mov(
        MovDestination::Y,
        MovOperation::BitReverse,
        MovSource::STATUS
    ),
    0b101_00000_010_10101
);

instr_test!(irq(true, false, 10), 0b110_00000_010_01010);
instr_test!(irq(false, true, 15), 0b110_00000_001_01111);

instr_test!(set(SetDestination::Y, 10), 0b111_00000_010_01010);
