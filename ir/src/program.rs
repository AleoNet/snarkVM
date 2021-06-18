// Copyright (C) 2019-2021 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use std::fmt;

use prost::Message;

use crate::{ir, Header, Instruction, MaskData, RepeatData};

use anyhow::*;

pub struct Program {
    pub header: Header,
    pub instructions: Vec<Instruction>,
}

impl Program {
    pub(crate) fn encode(&self) -> ir::Program {
        ir::Program {
            header: Some(self.header.encode()),
            instructions: self.instructions.iter().map(|x| x.encode()).collect(),
        }
    }

    pub(crate) fn decode(program: ir::Program) -> Result<Self> {
        Ok(Self {
            header: Header::decode(program.header.ok_or_else(|| anyhow!("missing header for program"))?)?,
            instructions: program
                .instructions
                .into_iter()
                .map(Instruction::decode)
                .collect::<Result<Vec<Instruction>>>()?,
        })
    }

    pub fn serialize(&self) -> Result<Vec<u8>> {
        let mut out = vec![];
        self.encode().encode(&mut out)?;
        Ok(out)
    }

    pub fn deserialize(input: &[u8]) -> Result<Self> {
        Self::decode(ir::Program::decode(input)?)
    }

    pub fn iter_functions<'a>(&self) -> impl Iterator<Item = &[Instruction]> {
        let mut iter: Vec<_> = self
            .header
            .function_offsets
            .windows(2)
            .map(|offsets| {
                assert_eq!(offsets.len(), 2);
                &self.instructions[offsets[0] as usize..offsets[1] as usize]
            })
            .collect();
        if !self.header.function_offsets.is_empty() {
            iter.push(&self.instructions[self.header.function_offsets.last().copied().unwrap() as usize..])
        }
        iter.into_iter()
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, instructions) in self.iter_functions().enumerate() {
            write!(f, "decl f{}:\n", i)?;
            let mut indent = 1usize;
            // indentation scheme assumes a well formed program (no inner masks/repeats are longer than parent mask/repeat/function body)
            let mut indent_stops = vec![];
            for (i, instruction) in instructions.iter().enumerate() {
                for _ in 0..indent {
                    write!(f, "  ")?;
                }
                instruction.fmt(f)?;
                if let Some(indent_stop) = indent_stops.last().copied() {
                    if indent_stop == i {
                        indent -= 1;
                    }
                    indent_stops.pop();
                }
                match instruction {
                    Instruction::Mask(MaskData { instruction_count, .. })
                    | Instruction::Repeat(RepeatData { instruction_count, .. }) => {
                        indent += 1;
                        indent_stops.push(i + *instruction_count as usize);
                    }
                    _ => (),
                }
            }
        }
        Ok(())
    }
}
