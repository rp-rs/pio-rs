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

#![no_std]
// PIO instr grouping is 3/5/3/5
#![allow(clippy::unusual_byte_groupings)]
#![allow(clippy::upper_case_acronyms)]

use arrayvec::ArrayVec;

/// Maximum program size in bytes.
///
/// See Chapter 3, Figure 38 for reference of the value.
const MAX_PROGRAM_SIZE: usize = 32;

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
    // RESERVED = 0b11,
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
pub enum InstructionOperands {
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
        relative: bool,
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
            } => (*destination as u8, *bit_count & 0b11111),
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
            InstructionOperands::IRQ {
                clear,
                wait,
                index,
                relative,
            } => {
                if *index > 7 {
                    panic!("invalid interrupt flags");
                }
                (
                    (*clear as u8) << 1 | (*wait as u8),
                    *index | (if *relative { 0b10000 } else { 0 }),
                )
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
pub struct Instruction {
    pub operands: InstructionOperands,
    pub delay: u8,
    pub side_set: Option<u8>,
}

impl Instruction {
    fn encode(&self, a: &Assembler) -> u16 {
        let mut data = self.operands.encode();

        if self.delay > a.delay_max {
            panic!(
                "delay of {} is greater than limit {}",
                self.delay, a.delay_max
            );
        }

        let side_set = if let Some(s) = self.side_set {
            if s > a.side_set.max {
                panic!("'side' set must be >=0 and <={}", a.side_set.max);
            }
            let s = (s as u16) << (5 - a.side_set.bits);
            if a.side_set.opt {
                s | 0b10000
            } else {
                s
            }
        } else if a.side_set.bits > 0 && !a.side_set.opt {
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

/// Data for 'side' set instruction parameters.
#[derive(Debug, Clone, Copy)]
pub struct SideSet {
    opt: bool,
    bits: u8,
    max: u8,
    pindirs: bool,
}

impl SideSet {
    pub fn new(opt: bool, bits: u8, pindirs: bool) -> SideSet {
        SideSet {
            opt,
            bits: bits + if opt { 1 } else { 0 },
            max: (1 << bits) - 1,
            pindirs,
        }
    }

    #[doc(hidden)]
    pub fn new_from_proc_macro(opt: bool, bits: u8, pindirs: bool) -> SideSet {
        SideSet {
            opt,
            bits,
            max: (1 << bits) - 1,
            pindirs,
        }
    }

    pub fn optional(&self) -> bool {
        self.opt
    }

    pub fn bits(&self) -> u8 {
        self.bits
    }

    pub fn pindirs(&self) -> bool {
        self.pindirs
    }
}

impl Default for SideSet {
    fn default() -> Self {
        SideSet::new(false, 0, false)
    }
}

/// A PIO Assembler. See chapter three of the [RP2040 Datasheet][].
///
/// [RP2040 Datasheet]: https://rptl.io/pico-datasheet
#[derive(Debug)]
pub struct Assembler {
    #[doc(hidden)]
    pub instructions: ArrayVec<Instruction, MAX_PROGRAM_SIZE>,
    #[doc(hidden)]
    pub side_set: SideSet,
    delay_max: u8,
}

impl Assembler {
    /// Create a new Assembler.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Assembler {
        Assembler::new_with_side_set(SideSet::default())
    }

    /// Create a new Assembler with `SideSet` settings.
    #[allow(clippy::new_without_default)]
    pub fn new_with_side_set(side_set: SideSet) -> Assembler {
        let delay_max = (1 << (5 - side_set.bits)) - 1;
        Assembler {
            instructions: ArrayVec::new(),
            side_set,
            delay_max,
        }
    }

    /// Assemble the program into PIO instructions.
    ///
    /// Takes optional pair of labels controlling the wrapping. The first label is the source (top) of the wrap while
    /// the second label is the target (bottom) of the wrap.
    ///
    /// If no labels are provided, the program wraps from after the last instruction to the top of the program.
    pub fn assemble(self, wrap: Option<(Label, Label)>) -> Program {
        let wrap = if let Some((source, target)) = wrap {
            let source = match source.state {
                LabelState::Bound(addr) => addr,
                LabelState::Unbound(_) => panic!("source label can't be unbound"),
            };
            let target = match target.state {
                LabelState::Bound(addr) => addr,
                LabelState::Unbound(_) => panic!("target label can't be unbound"),
            };

            Wrap {
                // We need to subtract one here as the label is positioned _after_ the instruction we want to wrap from,
                // but the hardware wants the index of that instruction.
                source: source - 1,
                target,
            }
        } else {
            Wrap {
                source: (self.instructions.len() - 1) as u8,
                target: 0,
            }
        };

        Program {
            instructions: self.instructions.iter().map(|i| i.encode(&self)).collect(),
            origin: None,
            wrap,
            side_set: self.side_set,
        }
    }
}

impl Assembler {
    /// Create a new unbound Label.
    pub fn label(&mut self) -> Label {
        Label {
            state: LabelState::Unbound(core::u8::MAX),
        }
    }

    /// Bind `label` to the current instruction position.
    pub fn bind(&mut self, label: &mut Label) {
        match label.state {
            LabelState::Bound(_) => panic!("cannot bind label twice"),
            LabelState::Unbound(mut patch) => {
                let resolved_address = self.instructions.len() as u8;
                while patch != core::u8::MAX {
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
        }
    );

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
        /// Emit an `irq` instruction using `clear` and `wait` with `index` which may be `relative`.
        irq(self, clear: bool, wait: bool, index: u8, relative: bool) {
            InstructionOperands::IRQ {
                clear,
                wait,
                index,
                relative,
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

/// Source and target for automatic program wrapping.
///
/// After the instruction at offset pointed by [`source`] has been executed, the program control flow jumps to the
/// instruction pointed by [`target`]. If the instruction is a jump, and the condition is true, the jump takes priority.
///
/// [`source`]: Self::source
/// [`target`]: Self::target
#[derive(Debug, Clone, Copy)]
pub struct Wrap {
    /// Source instruction for wrap.
    pub source: u8,
    /// Target instruction for wrap.
    pub target: u8,
}

/// Program ready to be executed by PIO hardware.

#[derive(Debug)]
pub struct Program {
    /// Assembled instructions.
    pub instructions: ArrayVec<u16, MAX_PROGRAM_SIZE>,
    /// Offset at which the program must be loaded.
    ///
    /// Most often 0 if defined. This might be needed when using data based JMPs.
    pub origin: Option<u8>,
    /// Wrapping behavior of this program.
    pub wrap: Wrap,
    /// Side-set info for this program.
    pub side_set: SideSet,
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
    ($name:ident ( $( $v:expr ),* ) , $b:expr, $side_set:expr) => {
        paste::paste! {
            #[test]
            fn [< test _ $name _ $b >]() {
                let mut a = Assembler::new_with_side_set($side_set);
                a.$name(
                    $( $v ),*
                );
                let a = a.assemble()[0];
                let b = $b;
                if a != b {
                    panic!("assertion failure: (left == right)\nleft:  {:#016b}\nright: {:#016b}", a, b);
                }
            }
        }
    };

    ($name:ident ( $( $v:expr ),* ) , $b:expr) => {
        instr_test!( $name ( $( $v ),* ), $b, SideSet::new(false, 0, false) );
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
    SideSet::new(false, 5, false)
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

instr_test!(irq(true, false, 0b11, false), 0b110_00000_010_00011);
instr_test!(irq(false, true, 0b111, true), 0b110_00000_001_10111);

instr_test!(set(SetDestination::Y, 10), 0b111_00000_010_01010);
