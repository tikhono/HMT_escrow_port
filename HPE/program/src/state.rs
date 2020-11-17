//! State types

use solana_program::{
    program_pack::{IsInitialized, Pack, Sealed},
    pubkey::Pubkey,
};
/// Lending pool state
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

impl Escrow {}

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
