use crate::{ir, Instruction};

use anyhow::*;

#[derive(Debug, Clone)]
pub struct Function {
    pub argument_start_variable: u32,
    pub instructions: Vec<Instruction>,
}

impl Function {
    pub(crate) fn decode(function: ir::Function) -> Result<Self> {
        Ok(Self {
            argument_start_variable: function.argument_start_variable,
            instructions: function
                .instructions
                .into_iter()
                .map(Instruction::decode)
                .collect::<Result<Vec<_>>>()?,
        })
    }

    pub(crate) fn encode(&self) -> ir::Function {
        ir::Function {
            argument_start_variable: self.argument_start_variable,
            instructions: self.instructions.iter().map(|x| x.encode()).collect(),
        }
    }
}
