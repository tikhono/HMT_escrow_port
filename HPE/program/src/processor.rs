//! Program state processor

use crate::error::EscrowError;
use crate::instruction::EscrowInstruction;
use num_traits::FromPrimitive;
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    decode_error::DecodeError,
    entrypoint::ProgramResult,
    info,
    program_error::{PrintProgramError, ProgramError},
    program_option::COption,
    program_pack::{IsInitialized, Pack},
    pubkey::Pubkey,
    sysvar::{rent::Rent, Sysvar},
};
/// Program state handler.
pub struct Processor {}

impl Processor {
    /// Processes an [InitializeEscrow](enum.TokenInstruction.html) instruction.
    pub fn process_initialize_escrow(accounts: &[AccountInfo]) -> ProgramResult {
        Ok(())
    }

    /// Processes an [Instruction](enum.Instruction.html).
    pub fn process(program_id: &Pubkey, accounts: &[AccountInfo], input: &[u8]) -> ProgramResult {
        let instruction = EscrowInstruction::unpack(input)?;

        match instruction {
            EscrowInstruction::InitializeEscrow {} => {
                info!("Instruction: Initialize");
                Self::process_initialize_escrow(accounts)
            }
        }
    }
}

impl PrintProgramError for EscrowError {
    fn print<E>(&self)
    where
        E: 'static + std::error::Error + DecodeError<E> + PrintProgramError + FromPrimitive,
    {
        match self {
            EscrowError::InvalidInstruction => info!("Error: invalid instruction"),
        }
    }
}
