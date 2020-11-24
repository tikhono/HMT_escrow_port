//! Program state processor

use crate::error::EscrowError;
use crate::instruction::EscrowInstruction;
use crate::state::*;
use num_traits::FromPrimitive;
use solana_program::program_error::ProgramError;
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    decode_error::DecodeError,
    entrypoint::ProgramResult,
    info,
    program_error::PrintProgramError,
    program_pack::{IsInitialized, Pack},
    pubkey::Pubkey,
};

/// Program state handler.
pub struct Processor {}

impl Processor {
    /// Processes an [InitializeEscrow](enum.TokenInstruction.html) instruction.
    pub fn process_initialize_escrow(accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let escrow_info = next_account_info(account_info_iter)?;
        let token_mint_info = next_account_info(account_info_iter)?;
        let token_account_info = next_account_info(account_info_iter)?;
        let reputation_oracle_info = next_account_info(account_info_iter)?;
        let reputation_oracle_token_account_info = next_account_info(account_info_iter)?;
        let recording_oracle_info = next_account_info(account_info_iter)?;
        let recording_oracle_token_account_info = next_account_info(account_info_iter)?;
        let launcher_info = next_account_info(account_info_iter)?;
        let canceler_info = next_account_info(account_info_iter)?;
        let canceler_token_account_info = next_account_info(account_info_iter)?;

        let escrow = Escrow::unpack_unchecked(&escrow_info.data.borrow())?;
        if escrow.is_initialized() {
            return Err(EscrowError::AlreadyInUse.into());
        }

        let obj = Escrow {
            state: EscrowState::Launched,
            token_mint: *token_mint_info.key,
            token_account: *token_account_info.key,
            reputation_oracle: *reputation_oracle_info.key,
            reputation_oracle_token_account: *reputation_oracle_token_account_info.key,
            reputation_oracle_stake: 0,
            recording_oracle: *recording_oracle_info.key,
            recording_oracle_token_account: *recording_oracle_token_account_info.key,
            recording_oracle_stake: 0,
            launcher: *launcher_info.key,
            canceler: *canceler_info.key,
            canceler_token_account: *canceler_token_account_info.key,
            paid_amount: 0,
        };

        Escrow::pack(obj, &mut escrow_info.data.borrow_mut())?;
        Ok(())
    }

    /// Processes an [BulkPayout](enum.TokenInstruction.html) instruction.
    pub fn process_bulk_payout(accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let escrow_info = next_account_info(account_info_iter)?;

        let mut escrow = Escrow::unpack_unchecked(&escrow_info.data.borrow())?;

        if escrow.state == EscrowState::Launched {
            return Err(EscrowError::InvalidInstruction.into()); //"Escrow in Launched status state"
        }
        if escrow.state == EscrowState::Paid {
            return Err(EscrowError::InvalidInstruction.into()); //"Escrow in Paid status state"
        }

        let bulk_paid = true;
        let balance = 10;
        if bulk_paid {
            if escrow.state == EscrowState::Pending {
                escrow.state = EscrowState::Partial;
            }
            if balance == 0 && escrow.state == EscrowState::Partial {
                escrow.state = EscrowState::Paid;
            }
        }
        Ok(())
    }

    /// Processes an [Complete](enum.TokenInstruction.html) instruction.
    pub fn process_complete(accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let escrow_info = next_account_info(account_info_iter)?;

        let mut escrow = Escrow::unpack_unchecked(&escrow_info.data.borrow())?;

        if escrow.state != EscrowState::Paid {
            return Err(EscrowError::InvalidInstruction.into()); //"Escrow not in Paid status state"
        }
        escrow.state = EscrowState::Completed;

        Ok(())
    }

    /// Processes an [Abort](enum.TokenInstruction.html) instruction.
    pub fn process_abort(accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let escrow_info = next_account_info(account_info_iter)?;

        let mut escrow = Escrow::unpack_unchecked(&escrow_info.data.borrow())?;

        if escrow.state == EscrowState::Completed {
            return Err(EscrowError::InvalidInstruction.into()); //"Escrow in Completed status state"
        }
        if escrow.state == EscrowState::Paid {
            return Err(EscrowError::InvalidInstruction.into()); //"Escrow in Paid status state"
        }
        //selfdestruct(canceler);
        //How to translate this to solana? Leave without money for rent???

        Ok(())
    }

    /// Processes an [Cancel](enum.TokenInstruction.html) instruction.
    pub fn process_cancel(accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let escrow_info = next_account_info(account_info_iter)?;

        let mut escrow = Escrow::unpack_unchecked(&escrow_info.data.borrow())?;

        if escrow.state == EscrowState::Completed {
            return Err(EscrowError::InvalidInstruction.into()); //"Escrow in Completed status state"
        }
        if escrow.state == EscrowState::Paid {
            return Err(EscrowError::InvalidInstruction.into()); //"Escrow in Paid status state"
        }
        /*
                uint256 balance = getBalance();
                require(balance != 0, "EIP20 contract out of funds");

                HMTokenInterface token = HMTokenInterface(eip20);
                bool success = token.transfer(canceler, balance);
        */
        escrow.state = EscrowState::Cancelled;

        Ok(())
    }

    /// Processes an [Instruction](enum.Instruction.html).
    pub fn process(_program_id: &Pubkey, accounts: &[AccountInfo], input: &[u8]) -> ProgramResult {
        let instruction = EscrowInstruction::unpack(input)?;

        match instruction {
            EscrowInstruction::InitializeEscrow {} => {
                info!("Instruction: Initialize");
                Self::process_initialize_escrow(accounts)
            }
            EscrowInstruction::BulkPayout {} => {
                info!("Instruction: BulkPayout");
                Self::process_bulk_payout(accounts)
            }
            EscrowInstruction::Complete {} => {
                info!("Instruction: Complete");
                Self::process_complete(accounts)
            }
            EscrowInstruction::Abort {} => {
                info!("Instruction: Abort");
                Self::process_complete(accounts)
            }
            EscrowInstruction::Cancel {} => {
                info!("Instruction: Cancel");
                Self::process_complete(accounts)
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
            EscrowError::AlreadyInUse => info!("Error: account already in use"),
            EscrowError::ExpectedMint => {
                info!("Error: Deserialized account is not an SPL Token mint")
            }
            EscrowError::ExpectedAccount => {
                info!("Error: Deserialized account is not an SPL Token account")
            }
        }
    }
}
