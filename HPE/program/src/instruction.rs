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
    /// Initializes a new account to hold tokens.  If this account is associated
    /// with the native mint then the token balance of the initialized account
    /// will be equal to the amount of SOL in the account. If this account is
    /// associated with another mint, that mint must be initialized before this
    /// command can succeed.
    ///
    /// The `InitializeAccount` instruction requires no signers and MUST be
    /// included within the same Transaction as the system program's
    /// `CreateAccount` instruction that creates the account being initialized.
    /// Otherwise another party can acquire ownership of the uninitialized
    /// account.
    ///
    /// Accounts expected by this instruction:
    ///
    ///   0. `[writable]`  The account to initialize.
    ///   1. `[]` The mint this account will be associated with.
    ///   2. `[]` The new account's owner/multisignature.
    ///   3. `[]` Rent sysvar
    InitializeEscrow,
}

impl EscrowInstruction {
    /// Unpacks
    pub fn unpack(input: &[u8]) -> Result<Self, ProgramError> {
        let (&tag, rest) = input.split_first().ok_or(EscrowError::InvalidInstruction)?;
        Ok(match tag {
            0 => {
                let (&decimals, rest) =
                    rest.split_first().ok_or(EscrowError::InvalidInstruction)?;
                Self::InitializeEscrow {}
            }
            1 => Self::InitializeEscrow,
            _ => return Err(EscrowError::InvalidInstruction.into()),
        })
    }
    /// Packs a [TokenInstruction](enum.TokenInstruction.html) into a byte buffer.
    pub fn pack(&self) -> Vec<u8> {
        let mut buf: Vec<u8> = Vec::with_capacity(size_of::<Self>());
        match self {
            Self::InitializeEscrow => buf.push(1),
        }
        buf
    }

    /*
    constructor(
    address _eip20,
    address payable _canceler,
    uint256 _duration,
    address[] memory _handlers
    ) public {
    eip20 = _eip20;
    status = EscrowStatuses.Launched;
    duration = _duration.add(block.timestamp); // solhint-disable-line not-rely-on-time
    launcher = msg.sender;
    canceler = _canceler;
    areTrustedHandlers[_canceler] = true;
    areTrustedHandlers[msg.sender] = true;
    addTrustedHandlers(_handlers);
    }
    */
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
