//! State types

use arrayref::{array_mut_ref, array_ref, array_refs, mut_array_refs};
use solana_program::{
    program_error::ProgramError,
    program_pack::{IsInitialized, Pack, Sealed},
    pubkey::Pubkey,
};

/// Escrow state.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum EscrowState {
    /// Escrow is not yet initialized
    Uninitialized,
    /// TODO
    Launched,
    /// TODO
    Pending,
    /// TODO
    Partial,
    /// TODO
    Paid,
    /// TODO
    Completed,
    /// TODO
    Cancelled,
}

impl Default for EscrowState {
    fn default() -> Self {
        EscrowState::Uninitialized
    }
}

/// Escrow data
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Escrow {
    ///Current status of escrow entity: Uninitialized, Launched, Pending, Partial, Paid, Complete, Cancelled
    pub state: EscrowState,
    ///Mint for the token handled by the escrow
    pub token_mint: Pubkey,
    ///Account to hold tokens for sendout, its owner should be escrow contract authority
    pub token_account: Pubkey,
    ///Pubkey of the reputation oracle
    pub reputation_oracle: Pubkey,
    ///Account for the reputation oracle to receive fee
    pub reputation_oracle_token_account: Pubkey,
    ///Reputation oracle fee (in percents)
    pub reputation_oracle_stake: u8,
    ///Pubkey of the recording oracle
    pub recording_oracle: Pubkey,
    ///Account for the recording oracle to receive fee
    pub recording_oracle_token_account: Pubkey,
    ///Recording oracle fee (in percents)
    pub recording_oracle_stake: u8,
    ///Launcher pubkey
    pub launcher: Pubkey,
    ///Canceler pubkey
    pub canceler: Pubkey,
    ///Account for the canceler to receive back tokens
    pub canceler_token_account: Pubkey,
    ///Amount in tokens already paid
    pub paid_amount: u64,
}

impl Sealed for Escrow {}
impl IsInitialized for Escrow {
    fn is_initialized(&self) -> bool {
        self.state != EscrowState::Uninitialized
    }
}

impl Pack for Escrow {
    const LEN: usize = 299;

    fn pack_into_slice(&self, output: &mut [u8]) {
        let output = array_mut_ref![output, 0, 299];
        let (
            token_mint,
            token_account,
            reputation_oracle,
            reputation_oracle_token_account,
            reputation_oracle_stake,
            recording_oracle,
            recording_oracle_token_account,
            recording_oracle_stake,
            launcher,
            canceler,
            canceler_token_account,
            paid_amount,
            status,
        ) = mut_array_refs![output, 32, 32, 32, 32, 1, 32, 32, 1, 32, 32, 32, 8, 1];
        token_mint.copy_from_slice(self.token_mint.as_ref());
        token_account.copy_from_slice(self.token_account.as_ref());
        reputation_oracle.copy_from_slice(self.reputation_oracle.as_ref());
        reputation_oracle_token_account
            .copy_from_slice(self.reputation_oracle_token_account.as_ref());
        reputation_oracle_stake[0] = self.reputation_oracle_stake;
        recording_oracle.copy_from_slice(self.recording_oracle.as_ref());
        recording_oracle_token_account
            .copy_from_slice(self.recording_oracle_token_account.as_ref());
        recording_oracle_stake[0] = self.recording_oracle_stake;
        launcher.copy_from_slice(self.launcher.as_ref());
        canceler.copy_from_slice(self.canceler.as_ref());
        canceler_token_account.copy_from_slice(self.canceler_token_account.as_ref());
        *paid_amount = self.paid_amount.to_le_bytes();
        self.state.pack_into_slice(&mut status[..]);
    }
    /// Unpacks a byte buffer into a [SwapInfo](struct.SwapInfo.html).
    fn unpack_from_slice(input: &[u8]) -> Result<Self, ProgramError> {
        let input = array_ref![input, 0, 299];
        #[allow(clippy::ptr_offset_with_cast)]
        let (
            token_mint,
            token_account,
            reputation_oracle,
            reputation_oracle_token_account,
            reputation_oracle_stake,
            recording_oracle,
            recording_oracle_token_account,
            recording_oracle_stake,
            launcher,
            canceler,
            canceler_token_account,
            paid_amount,
            status,
        ) = array_refs![input, 32, 32, 32, 32, 1, 32, 32, 1, 32, 32, 32, 8, 1];
        Ok(Self {
            token_mint: Pubkey::new_from_array(*token_mint),
            token_account: Pubkey::new_from_array(*token_account),

            reputation_oracle: Pubkey::new_from_array(*reputation_oracle),
            reputation_oracle_token_account: Pubkey::new_from_array(
                *reputation_oracle_token_account,
            ),
            reputation_oracle_stake: reputation_oracle_stake[0],

            recording_oracle: Pubkey::new_from_array(*recording_oracle),
            recording_oracle_token_account: Pubkey::new_from_array(*recording_oracle_token_account),
            recording_oracle_stake: recording_oracle_stake[0],

            launcher: Pubkey::new_from_array(*launcher),
            canceler: Pubkey::new_from_array(*canceler),
            canceler_token_account: Pubkey::new_from_array(*canceler_token_account),
            paid_amount: u64::from_le_bytes(*paid_amount),
            state: EscrowState::unpack_from_slice(status)?,
        })
    }
}

impl Sealed for EscrowState {}
impl Pack for EscrowState {
    const LEN: usize = 8;

    /// Pack SwapCurve into a byte buffer
    fn pack_into_slice(&self, output: &mut [u8]) {
        output[0] = *self as u8;
    }
    fn unpack_from_slice(input: &[u8]) -> Result<Self, ProgramError> {
        match input[0] {
            1u8 => Ok(EscrowState::Launched),
            2u8 => Ok(EscrowState::Uninitialized),
            3u8 => Ok(EscrowState::Cancelled),
            4u8 => Ok(EscrowState::Completed),
            5u8 => Ok(EscrowState::Paid),
            6u8 => Ok(EscrowState::Partial),
            7u8 => Ok(EscrowState::Pending),
            _ => Err(ProgramError::InvalidAccountData),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use arrayref::{array_mut_ref, array_ref, array_refs, mut_array_refs};
    use solana_program::{
        program_error::ProgramError,
        program_pack::{IsInitialized, Pack, Sealed},
        pubkey::Pubkey,
    };
    #[test]
    fn test_escrow_state_packing() {}

    #[test]
    fn test_instruction_packing() {
        let obj = Escrow {
            state: EscrowState::Launched,
            token_mint: Pubkey::new_from_array([
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32,
            ]),
            token_account: Pubkey::new_from_array([
                2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32,
            ]),
            reputation_oracle: Pubkey::new_from_array([
                3, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32,
            ]),
            reputation_oracle_token_account: Pubkey::new_from_array([
                4, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32,
            ]),
            reputation_oracle_stake: 10,
            recording_oracle: Pubkey::new_from_array([
                5, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32,
            ]),
            recording_oracle_token_account: Pubkey::new_from_array([
                6, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32,
            ]),
            recording_oracle_stake: 10,
            launcher: Pubkey::new_from_array([
                7, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32,
            ]),
            canceler: Pubkey::new_from_array([
                8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32,
            ]),
            canceler_token_account: Pubkey::new_from_array([
                9, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32,
            ]),
            paid_amount: 10,
        };
        let mut packed_obj: [u8; 299] = [0; 299];
        Escrow::pack(obj, &mut packed_obj).unwrap();
        let unpacked_obj = Escrow::unpack(&packed_obj).unwrap();
        assert_eq!(unpacked_obj, obj);
    }
}
