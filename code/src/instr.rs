use std::fmt::{Debug, Display};
use derive::Instruction;

pub trait Instruction : Debug + Display {
    fn inputs(&self) -> Vec<&InsIn>;
    fn inputs_mut(&mut self) -> Vec<&mut InsIn>;

    fn outputs(&self) -> Vec<&InsOut>;
    fn outputs_mut(&mut self) -> Vec<&mut InsOut>;

    fn lexer_translate(&self) -> Option<Vec<Ins>>;
}

#[derive(Debug, Clone)]
pub enum InsIn {
    None,
    Var(String),
    Int(i64),
    Float(f64),
    Str(String),
    Builtin(String),
}

impl Display for InsIn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InsIn::None => write!(f, "_"),
            InsIn::Var(val) => write!(f, "{}", val),
            InsIn::Int(val) => write!(f, "{}", val),
            InsIn::Float(val) => write!(f, "{}", val),
            InsIn::Str(val) => write!(f, "\"{}\"", val),
            InsIn::Builtin(val) => write!(f, "{}", val),
        }
    }
}

impl Default for InsIn {
    fn default() -> Self {
        Self::None
    }
}

pub type InsOut = String;

type In = InsIn;
type Out = InsOut;
type Sel = String;

#[derive(Debug, Instruction)]
pub enum Ins {
    #[n]
    Read(Out, In, In),
    Write(In, In, In),
    Draw(Sel, In, In, In, In, In, In),
    Print(In),
    PrintChar(In),
    Format(In),

    DrawFlush(In),
    PrintFlush(In),
    #[n]
    GetLink(Out, In),
    Control(Sel, In, In, In, In),
    #[n]
    Radar(Sel, Sel, Sel, Sel, In, In, Out),
    #[n]
    Sensor(Out, In, In),

    #[n]
    Set(Out, In),
    #[n]
    Op(Out, Sel, In, In),
    #[n]
    Lookup(Sel, Out, In),
    #[n]
    PackColor(Out, In, In, In, In),
    #[n]
    UnpackColor(Out, Out, Out, Out, In),

    Wait(In),
    Stop(),
    End(),
    Jump(In, In, In, In),

    UBind(In),
    UControl(Sel, In, In, In, In, In),
    #[n]
    UControlGetBlock(Sel, In, In, Out, Out, In),
    #[n]
    UControlWithin(Sel, In, In, In, Out),
    #[n]
    URadar(Sel, Sel, Sel, Sel, In, In, Out),

    #[dyn_ins]
    Dyn(Box<dyn Instruction>),
}
