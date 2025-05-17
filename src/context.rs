use smol_str::{format_smolstr, SmolStr};
use code::instr::Ins;
use crate::tree::Tree;

#[derive(Debug, Default)]
pub struct Globals {
    pub val: Tree<SmolStr, ()>,
    pub ty: Tree<SmolStr, ()>,
}

#[derive(Debug, Default)]
pub struct Ctx {
    instructions: Vec<Ins>,
    modules: Vec<(SmolStr, Vec<Ins>)>,
    tmp_counter: usize,
    pub globals: Globals,
}

impl Ctx {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn tmp(&mut self) -> SmolStr {
        format_smolstr!("__tmp{}", self.tmp_num())
    }

    pub fn tmp_num(&mut self) -> usize {
        self.tmp_counter += 1;
        self.tmp_counter
    }

    pub fn emit(&mut self, ins: Ins) {
        self.instructions.push(ins);
    }

    pub fn emit_all(&mut self, ins: impl IntoIterator<Item = Ins>) {
        self.instructions.extend(ins);
    }
    
    pub fn module<T>(&mut self, name: SmolStr, func: impl FnOnce(&mut Self) -> T) -> T {
        let curr = std::mem::take(&mut self.instructions);
        let result = func(self);
        self.modules.push((name, std::mem::replace(&mut self.instructions, curr)));
        result
    }
}
