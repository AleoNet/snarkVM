// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/// The RocksDB map prefix broken down into the entry category and the specific type of the entry.
// Note: the order of these variants can be changed at any point in time.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum MapID {
    Block(BlockMap),
    Deployment(DeploymentMap),
    Execution(ExecutionMap),
    Fee(FeeMap),
    Transaction(TransactionMap),
    Transition(TransitionMap),
    TransitionInput(TransitionInputMap),
    TransitionOutput(TransitionOutputMap),
    Program(ProgramMap),
    #[cfg(test)]
    Test(TestMap),
}

impl From<MapID> for u16 {
    fn from(id: MapID) -> u16 {
        match id {
            MapID::Block(id) => id as u16,
            MapID::Deployment(id) => id as u16,
            MapID::Execution(id) => id as u16,
            MapID::Fee(id) => id as u16,
            MapID::Transaction(id) => id as u16,
            MapID::Transition(id) => id as u16,
            MapID::TransitionInput(id) => id as u16,
            MapID::TransitionOutput(id) => id as u16,
            MapID::Program(id) => id as u16,
            #[cfg(test)]
            MapID::Test(id) => id as u16,
        }
    }
}

/// The RocksDB map prefix for block-related entries.
// Note: the order of these variants can be changed at any point in time,
// as long as the corresponding DataID values remain the same.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum BlockMap {
    StateRoot = DataID::BlockStateRootMap as u16,
    ReverseStateRoot = DataID::BlockReverseStateRootMap as u16,
    ID = DataID::BlockIDMap as u16,
    ReverseID = DataID::BlockReverseIDMap as u16,
    Header = DataID::BlockHeaderMap as u16,
    Authority = DataID::BlockAuthorityMap as u16,
    Transactions = DataID::BlockTransactionsMap as u16,
    ConfirmedTransactions = DataID::BlockConfirmedTransactionsMap as u16,
    Ratifications = DataID::BlockRatificationsMap as u16,
    CoinbaseSolution = DataID::BlockCoinbaseSolutionMap as u16,
    CoinbasePuzzleCommitment = DataID::BlockCoinbasePuzzleCommitmentMap as u16,
}

/// The RocksDB map prefix for deployment-related entries.
// Note: the order of these variants can be changed at any point in time,
// as long as the corresponding DataID values remain the same.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum DeploymentMap {
    ID = DataID::DeploymentIDMap as u16,
    Edition = DataID::DeploymentEditionMap as u16,
    ReverseID = DataID::DeploymentReverseIDMap as u16,
    Owner = DataID::DeploymentOwnerMap as u16,
    Program = DataID::DeploymentProgramMap as u16,
    VerifyingKey = DataID::DeploymentVerifyingKeyMap as u16,
    Certificate = DataID::DeploymentCertificateMap as u16,
}

/// The RocksDB map prefix for execution-related entries.
// Note: the order of these variants can be changed at any point in time,
// as long as the corresponding DataID values remain the same.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum ExecutionMap {
    ID = DataID::ExecutionIDMap as u16,
    ReverseID = DataID::ExecutionReverseIDMap as u16,
    Inclusion = DataID::ExecutionInclusionMap as u16,
}

/// The RocksDB map prefix for fee-related entries.
// Note: the order of these variants can be changed at any point in time,
// as long as the corresponding DataID values remain the same.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum FeeMap {
    Fee = DataID::FeeFeeMap as u16,
    ReverseFee = DataID::FeeReverseFeeMap as u16,
}

/// The RocksDB map prefix for transition input entries.
// Note: the order of these variants can be changed at any point in time,
// as long as the corresponding DataID values remain the same.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum TransitionInputMap {
    ID = DataID::InputIDMap as u16,
    ReverseID = DataID::InputReverseIDMap as u16,
    Constant = DataID::InputConstantMap as u16,
    Public = DataID::InputPublicMap as u16,
    Private = DataID::InputPrivateMap as u16,
    Record = DataID::InputRecordMap as u16,
    RecordTag = DataID::InputRecordTagMap as u16,
    ExternalRecord = DataID::InputExternalRecordMap as u16,
}

/// The RocksDB map prefix for transition output entries.
// Note: the order of these variants can be changed at any point in time,
// as long as the corresponding DataID values remain the same.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum TransitionOutputMap {
    ID = DataID::OutputIDMap as u16,
    ReverseID = DataID::OutputReverseIDMap as u16,
    Constant = DataID::OutputConstantMap as u16,
    Public = DataID::OutputPublicMap as u16,
    Private = DataID::OutputPrivateMap as u16,
    Record = DataID::OutputRecordMap as u16,
    RecordNonce = DataID::OutputRecordNonceMap as u16,
    ExternalRecord = DataID::OutputExternalRecordMap as u16,
}

/// The RocksDB map prefix for transaction-related entries.
// Note: the order of these variants can be changed at any point in time,
// as long as the corresponding DataID values remain the same.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum TransactionMap {
    ID = DataID::TransactionIDMap as u16,
}

/// The RocksDB map prefix for transition-related entries.
// Note: the order of these variants can be changed at any point in time,
// as long as the corresponding DataID values remain the same.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum TransitionMap {
    Locator = DataID::TransitionLocatorMap as u16,
    Finalize = DataID::TransitionFinalizeMap as u16,
    TPK = DataID::TransitionTPKMap as u16,
    ReverseTPK = DataID::TransitionReverseTPKMap as u16,
    TCM = DataID::TransitionTCMMap as u16,
    ReverseTCM = DataID::TransitionReverseTCMMap as u16,
}

/// The RocksDB map prefix for program-related entries.
// Note: the order of these variants can be changed at any point in time,
// as long as the corresponding DataID values remain the same.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum ProgramMap {
    ProgramID = DataID::ProgramIDMap as u16,
    MappingID = DataID::MappingIDMap as u16,
    KeyValueID = DataID::KeyValueIDMap as u16,
    Key = DataID::KeyMap as u16,
    Value = DataID::ValueMap as u16,
}

/// The RocksDB map prefix for test-related entries.
// Note: the order of these variants can be changed at any point in time.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum TestMap {
    Test = DataID::Test as u16,
    Test2 = DataID::Test2 as u16,
    Test3 = DataID::Test3 as u16,
    Test4 = DataID::Test4 as u16,
}

/// The RocksDB map prefix.
// Note: the order of these variants can NOT be changed once the database is populated:
// - any new variant MUST be added as the last one (ignoring the Test one)
// - any deprecated variant MUST remain in its position (it can't be removed)
#[allow(clippy::enum_variant_names)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u16)]
enum DataID {
    // Block
    BlockStateRootMap,
    BlockReverseStateRootMap,
    BlockIDMap,
    BlockReverseIDMap,
    BlockHeaderMap,
    BlockAuthorityMap,
    BlockTransactionsMap,
    BlockConfirmedTransactionsMap,
    BlockRatificationsMap,
    BlockCoinbaseSolutionMap,
    BlockCoinbasePuzzleCommitmentMap,
    // Deployment
    DeploymentIDMap,
    DeploymentEditionMap,
    DeploymentReverseIDMap,
    DeploymentOwnerMap,
    DeploymentProgramMap,
    DeploymentVerifyingKeyMap,
    DeploymentCertificateMap,
    // Execution
    ExecutionIDMap,
    ExecutionReverseIDMap,
    ExecutionInclusionMap,
    // Fee
    FeeFeeMap,
    FeeReverseFeeMap,
    // Input
    InputIDMap,
    InputReverseIDMap,
    InputConstantMap,
    InputPublicMap,
    InputPrivateMap,
    InputRecordMap,
    InputRecordTagMap,
    InputExternalRecordMap,
    // Output
    OutputIDMap,
    OutputReverseIDMap,
    OutputConstantMap,
    OutputPublicMap,
    OutputPrivateMap,
    OutputRecordMap,
    OutputRecordNonceMap,
    OutputExternalRecordMap,
    // Transaction
    TransactionIDMap,
    // Transition
    TransitionLocatorMap,
    TransitionFinalizeMap,
    TransitionTPKMap,
    TransitionReverseTPKMap,
    TransitionTCMMap,
    TransitionReverseTCMMap,
    // Program
    ProgramIDMap,
    MappingIDMap,
    KeyValueIDMap,
    KeyMap,
    ValueMap,

    // Testing
    #[cfg(test)]
    Test,
    #[cfg(test)]
    Test2,
    #[cfg(test)]
    Test3,
    #[cfg(test)]
    Test4,
}
