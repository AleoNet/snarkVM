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

use crate::{AccountError, ProgramError, RecordError, TransactionError};
use snarkvm_algorithms::{
    CRHError,
    CommitmentError,
    EncryptionError,
    MerkleError,
    PRFError,
    SNARKError,
    SignatureError,
};
use snarkvm_fields::ConstraintFieldError;
use snarkvm_parameters::ParameterError;

#[derive(Debug, Error)]
pub enum DPCError {
    #[error("{}", _0)]
    AccountError(#[from] AccountError),

    #[error("{}", _0)]
    AnyhowError(#[from] anyhow::Error),

    #[error("{}", _0)]
    CommitmentError(#[from] CommitmentError),

    #[error("{}", _0)]
    ConstraintFieldError(#[from] ConstraintFieldError),

    #[error("{}", _0)]
    CRHError(#[from] CRHError),

    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),

    #[error("{}", _0)]
    EncryptionError(#[from] EncryptionError),

    #[error(
        "Invalid transaction kernel: network = {}, |serial numbers| = {}, |commitments| = {}, |ciphertext_ids| = {}",
        _0,
        _1,
        _2,
        _3
    )]
    InvalidKernel(u16, usize, usize, usize),

    #[error("Invalid number of inputs - (current: {}, max: {})", _0, _1)]
    InvalidNumberOfInputs(usize, usize),

    #[error("Invalid number of outputs - (current: {}, max: {})", _0, _1)]
    InvalidNumberOfOutputs(usize, usize),

    #[error("{}", _0)]
    FromHexError(#[from] hex::FromHexError),

    #[error("{}", _0)]
    MerkleError(#[from] MerkleError),

    #[error("{}", _0)]
    Message(String),

    #[error("missing inner circuit proving key")]
    MissingInnerProvingKey,

    #[error("Missing circuit - {}", _0)]
    MissingCircuit(&'static str),

    #[error("missing noop circuit")]
    MissingNoopCircuit,

    #[error("missing outer circuit proving key")]
    MissingOuterProvingKey,

    #[error("{}", _0)]
    ParameterError(#[from] ParameterError),

    #[error("{}", _0)]
    ProgramError(#[from] ProgramError),

    #[error("{}", _0)]
    PRFError(#[from] PRFError),

    #[error("{}", _0)]
    RecordError(#[from] RecordError),

    #[error("{}", _0)]
    SignatureError(#[from] SignatureError),

    #[error("{}", _0)]
    SNARKError(#[from] SNARKError),

    #[error("{}", _0)]
    TransactionError(#[from] TransactionError),
}

impl From<std::io::Error> for DPCError {
    fn from(error: std::io::Error) -> Self {
        DPCError::Crate("std::io", format!("{:?}", error))
    }
}

impl From<DPCError> for std::io::Error {
    fn from(error: DPCError) -> Self {
        std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", error))
    }
}
