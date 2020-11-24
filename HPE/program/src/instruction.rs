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
}

impl EscrowInstruction {
    /// Unpacks
    pub fn unpack(input: &[u8]) -> Result<Self, ProgramError> {
        let (&tag, _rest) = input.split_first().ok_or(EscrowError::InvalidInstruction)?;
        Ok(match tag {
            1 => Self::InitializeEscrow,
            2 => Self::BulkPayout,
            3 => Self::Complete,
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
        }
        buf
    }
}

/// Creates a `InitializeAccount` instruction.
pub fn initialize_escrow(
    token_program_id: &Pubkey,
    account_pubkey: &Pubkey,
    mint_pubkey: &Pubkey,
    owner_pubkey: &Pubkey,
) -> Result<Instruction, ProgramError> {
    let data = EscrowInstruction::InitializeEscrow.pack();

    let accounts = vec![
        AccountMeta::new(*account_pubkey, false),
        AccountMeta::new_readonly(*mint_pubkey, false),
        AccountMeta::new_readonly(*owner_pubkey, false),
        AccountMeta::new_readonly(sysvar::rent::id(), false),
    ];

    Ok(Instruction {
        program_id: *token_program_id,
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
    }
}
