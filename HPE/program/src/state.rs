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
    pub status: EscrowState,
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
        self.status != EscrowState::Uninitialized
    }
}

impl Pack for Escrow {
    const LEN: usize = 376;

    fn pack_into_slice(&self, output: &mut [u8]) {
        let output = array_mut_ref![output, 0, 376];
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
        ) = mut_array_refs![output, 32, 32, 32, 32, 8, 32, 32, 8, 32, 32, 32, 64, 8];
        token_mint.copy_from_slice(self.token_mint.as_ref());
        token_account.copy_from_slice(self.token_account.as_ref());
        reputation_oracle.copy_from_slice(self.reputation_oracle.as_ref());
        reputation_oracle_token_account
            .copy_from_slice(self.reputation_oracle_token_account.as_ref());
        reputation_oracle_stake[0] = self.recording_oracle_stake;
        recording_oracle.copy_from_slice(self.recording_oracle_token_account.as_ref());
        recording_oracle_token_account
            .copy_from_slice(self.recording_oracle_token_account.as_ref());
        recording_oracle_stake[0] = self.recording_oracle_stake;
        launcher.copy_from_slice(self.launcher.as_ref());
        canceler.copy_from_slice(self.canceler.as_ref());
        canceler_token_account.copy_from_slice(self.canceler_token_account.as_ref());
        paid_amount.clone_from_slice(&&self.paid_amount.to_le_bytes().as_ref());
        self.status.pack_into_slice(&mut status[..]);
    }
    /// Unpacks a byte buffer into a [SwapInfo](struct.SwapInfo.html).
    fn unpack_from_slice(input: &[u8]) -> Result<Self, ProgramError> {
        let input = array_ref![input, 0, 376];
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
        ) = array_refs![input, 32, 32, 32, 32, 8, 32, 32, 8, 32, 32, 32, 64, 8];
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
            paid_amount: **paid_amount,
            status: EscrowState::unpack_from_slice(status)?,
        })
    }
}

impl Sealed for EscrowState {}
impl Pack for EscrowState {
    /// Size of encoding of all curve parameters, which include fees and any other
    /// constants used to calculate swaps, deposits, and withdrawals.
    /// This includes 1 byte for the type, and 72 for the calculator to use as
    /// it needs.  Some calculators may be smaller than 72 bytes.
    const LEN: usize = 73;

    /// Pack SwapCurve into a byte buffer
    fn pack_into_slice(&self, output: &mut [u8]) {
        let output = array_mut_ref![output, 0, 73];
        let (curve_type, calculator) = mut_array_refs![output, 1, 72];
        curve_type[0] = self.curve_type as u8;
        self.calculator.pack_into_slice(&mut calculator[..]);
    }

    /// Unpacks a byte buffer into a SwapCurve
    fn unpack_from_slice(input: &[u8]) -> Result<Self, ProgramError> {
        let input = array_ref![input, 0, 73];
        #[allow(clippy::ptr_offset_with_cast)]
        let (curve_type, calculator) = array_refs![input, 1, 72];
        let curve_type = curve_type[0].try_into()?;
        Ok(Self {
            curve_type,
            calculator: match curve_type {
                CurveType::ConstantProduct => {
                    Box::new(ConstantProductCurve::unpack_from_slice(calculator)?)
                }
                CurveType::Flat => Box::new(FlatCurve::unpack_from_slice(calculator)?),
                CurveType::Stable => Box::new(StableCurve::unpack_from_slice(calculator)?),
            },
        })
    }
}
