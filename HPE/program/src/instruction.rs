//! Instruction types

use crate::error::EscrowError;
use solana_program::{
    instruction::{AccountMeta, Instruction},
    program_error::ProgramError,
    pubkey::Pubkey,
    sysvar,
};
use std::mem::size_of;
/// Instructions supported by the lending program.
#[repr(C)]
#[derive(Clone, Debug, PartialEq)]
pub enum EscrowInstruction {
    /// Initializes a new Escrow. Compilation of Constructor and Setup from solidity codebase
    InitializeEscrow,

    /// Bulk payout
    BulkPayout,

    /// Complete
    Complete,

    /// Abort
    Abort,

    /// Cancel
    Cancel,
}

impl EscrowInstruction {
    /// Unpacks a byte buffer into [EscrowInstruction](enum.EscrowInstruction.html).
    pub fn unpack(input: &[u8]) -> Result<Self, ProgramError> {
        let (&tag, _rest) = input.split_first().ok_or(EscrowError::InvalidInstruction)?;
        Ok(match tag {
            1 => Self::InitializeEscrow,
            2 => Self::BulkPayout,
            3 => Self::Complete,
            4 => Self::Abort,
            5 => Self::Cancel,
            _ => return Err(EscrowError::InvalidInstruction.into()),
        })
    }

    /// Packs a [EscrowInstruction](enum.EscrowInstruction.html) into a byte buffer.
    pub fn pack(&self) -> Vec<u8> {
        let mut buf: Vec<u8> = Vec::with_capacity(size_of::<Self>());
        match self {
            Self::InitializeEscrow => buf.push(1),
            Self::BulkPayout => buf.push(2),
            Self::Complete => buf.push(3),
            Self::Abort => buf.push(4),
            Self::Cancel => buf.push(5),
        }
        buf
    }
}

/// Creates a `InitializeAccount` instruction.
pub fn initialize_escrow(
    program_id: Pubkey,
    state: &Pubkey,
    token_mint: &Pubkey,
    token_account: &Pubkey,
    reputation_oracle: &Pubkey,
    reputation_oracle_token_account: &Pubkey,
    recording_oracle: &Pubkey,
    recording_oracle_token_account: &Pubkey,
    launcher: &Pubkey,
    canceler: &Pubkey,
    canceler_token_account: &Pubkey,
) -> Result<Instruction, ProgramError> {
    let data = EscrowInstruction::InitializeEscrow.pack();

    let accounts = vec![
        AccountMeta::new(*state, false),
        AccountMeta::new_readonly(*token_mint, false),
        AccountMeta::new_readonly(*token_account, false),
        AccountMeta::new_readonly(*reputation_oracle, false),
        AccountMeta::new_readonly(*reputation_oracle_token_account, false),
        AccountMeta::new_readonly(*recording_oracle, false),
        AccountMeta::new_readonly(*recording_oracle_token_account, false),
        AccountMeta::new_readonly(*launcher, false),
        AccountMeta::new_readonly(*canceler, false),
        AccountMeta::new_readonly(*canceler_token_account, false),
    ];

    Ok(Instruction {
        program_id,
        accounts,
        data,
    })
}

/// Creates a `Complete` instruction.
pub fn complete_escrow(program_id: Pubkey, state: &Pubkey) -> Result<Instruction, ProgramError> {
    let data = EscrowInstruction::InitializeEscrow.pack();

    let accounts = vec![AccountMeta::new(*state, false)];

    Ok(Instruction {
        program_id,
        accounts,
        data,
    })
}

/// Creates a `BulkPayout` instruction.
pub fn bulk_payout(program_id: Pubkey, state: &Pubkey) -> Result<Instruction, ProgramError> {
    let data = EscrowInstruction::InitializeEscrow.pack();

    let accounts = vec![AccountMeta::new(*state, false)];

    Ok(Instruction {
        program_id,
        accounts,
        data,
    })
}

/// Creates a `Abort` instruction.
pub fn abort(program_id: Pubkey, state: &Pubkey) -> Result<Instruction, ProgramError> {
    let data = EscrowInstruction::InitializeEscrow.pack();

    let accounts = vec![AccountMeta::new(*state, false)];

    Ok(Instruction {
        program_id,
        accounts,
        data,
    })
}

/// Creates a `Cancel` instruction.
pub fn cancel(program_id: Pubkey, state: &Pubkey) -> Result<Instruction, ProgramError> {
    let data = EscrowInstruction::InitializeEscrow.pack();

    let accounts = vec![AccountMeta::new(*state, false)];

    Ok(Instruction {
        program_id,
        accounts,
        data,
    })
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_instruction_packing() {
        let check = EscrowInstruction::InitializeEscrow;
        let packed = check.pack();
        let expect = Vec::from([1u8]);
        assert_eq!(packed, expect);
        let unpacked = EscrowInstruction::unpack(&expect).unwrap();
        assert_eq!(unpacked, check);

        let check = EscrowInstruction::BulkPayout;
        let packed = check.pack();
        let expect = Vec::from([2u8]);
        assert_eq!(packed, expect);
        let unpacked = EscrowInstruction::unpack(&expect).unwrap();
        assert_eq!(unpacked, check);

        let check = EscrowInstruction::Complete;
        let packed = check.pack();
        let expect = Vec::from([3u8]);
        assert_eq!(packed, expect);
        let unpacked = EscrowInstruction::unpack(&expect).unwrap();
        assert_eq!(unpacked, check);

        let check = EscrowInstruction::Abort;
        let packed = check.pack();
        let expect = Vec::from([4u8]);
        assert_eq!(packed, expect);
        let unpacked = EscrowInstruction::unpack(&expect).unwrap();
        assert_eq!(unpacked, check);

        let check = EscrowInstruction::Cancel;
        let packed = check.pack();
        let expect = Vec::from([5u8]);
        assert_eq!(packed, expect);
        let unpacked = EscrowInstruction::unpack(&expect).unwrap();
        assert_eq!(unpacked, check);
    }
}
