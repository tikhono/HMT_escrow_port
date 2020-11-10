//! The Uniswap invariant calculator.

use solana_program::{
    program_error::ProgramError,
    program_pack::{IsInitialized, Pack, Sealed},
};

use crate::curve::calculator::{
    calculate_fee, map_zero_to_none, CurveCalculator, DynPack, SwapResult,
};
use arrayref::{array_mut_ref, array_ref, array_refs, mut_array_refs};
use num_traits::checked_pow;
use std::convert::TryFrom;

/// StableCurve struct implementing CurveCalculator
#[derive(Clone, Debug, Default, PartialEq)]
pub struct StableCurve {
    /// Trade fee numerator
    pub trade_fee_numerator: u64,
    /// Trade fee denominator
    pub trade_fee_denominator: u64,
    /// Owner trade fee numerator
    pub owner_trade_fee_numerator: u64,
    /// Owner trade fee denominator
    pub owner_trade_fee_denominator: u64,
    /// Owner withdraw fee numerator
    pub owner_withdraw_fee_numerator: u64,
    /// Owner withdraw fee denominator
    pub owner_withdraw_fee_denominator: u64,
    /// Host trading fee numerator
    pub host_fee_numerator: u64,
    /// Host trading fee denominator
    pub host_fee_denominator: u64,
    /// Amplifier constant
    pub amp: u64,
}

/// Compute stable swap invariant (D)
/// Equation:
/// A * sum(x_i) * n**n + D = A * D * n**n + D**(n+1) / (n**n * prod(x_i))
fn compute_d(amp: u128, amount_a: u128, amount_b: u128) -> Option<u128> {
    // XXX: Curve uses u256
    // TODO: Handle overflows
    let n_coins: u128 = 2; // n
    let sum_x = amount_a.checked_add(amount_b)?; // sum(x_i), a.k.a S
    if sum_x == 0 {
        Some(0)
    } else {
        let mut d_prev: u128;
        let mut d = sum_x;
        let leverage = amp.checked_mul(n_coins)?; // A * n
                                                  // Newton's method to approximate D
        for _ in 0..128 {
            let mut d_p = d;
            d_p = d_p.checked_mul(d.checked_div(amount_a.checked_mul(n_coins)?)?)?;
            d_p = d_p.checked_mul(d.checked_div(amount_b.checked_mul(n_coins)?)?)?;
            d_prev = d;
            d = (leverage * sum_x + d_p * n_coins) * d / ((leverage - 1) * d + (n_coins + 1) * d_p);
            // Equality with the precision of 1
            if d > d_p {
                if d.checked_sub(d_prev)? <= 1 {
                    break;
                }
            } else if d_prev.checked_sub(d)? <= 1 {
                break;
            }
        }

        Some(d)
    }
}

/// Compute swap amount `y` in proportion to `x`
/// Solve for y:
/// y**2 + y * (sum' - (A*n**n - 1) * D / (A * n**n)) = D ** (n + 1) / (n ** (2 * n) * prod' * A)
/// y**2 + b*y = c
fn compute_y(amp: u128, x: u128, d: u128) -> Option<u128> {
    // XXX: Curve uses u256
    // TODO: Handle overflows
    let n_coins: u128 = 2;
    let leverage = amp.checked_mul(n_coins)?; // A * n

    // sum' = prod' = x
    // c =  D ** (n + 1) / (n ** (2 * n) * prod' * A)
    let c = checked_pow(d, 3)?
        .checked_div(x.checked_mul(checked_pow(n_coins, 2)?.checked_mul(leverage)?)?)?;
    // b = sum' - (A*n**n - 1) * D / (A * n**n)
    let b = x.checked_add(d.checked_div(leverage)?)?; // d is subtracted on line 82

    // Solve for y by approximating: y**2 + b*y = c
    let mut y_prev: u128;
    let mut y = d;
    for _ in 0..128 {
        y_prev = y;
        y = (y * y + c) / (2 * y + b - d);
        if y > y_prev {
            if y.checked_sub(y_prev)? <= 1 {
                break;
            }
        } else if y_prev.checked_sub(y)? <= 1 {
            break;
        }
    }
    Some(y)
}

impl CurveCalculator for StableCurve {
    /// Stable curve
    fn swap(
        &self,
        source_amount: u128,
        swap_source_amount: u128,
        swap_destination_amount: u128,
    ) -> Option<SwapResult> {
        let y = compute_y(
            self.amp as u128,
            swap_source_amount.checked_add(source_amount)?,
            compute_d(
                self.amp as u128,
                swap_source_amount,
                swap_destination_amount,
            )?,
        )?;
        let dy = swap_destination_amount.checked_sub(y)?;
        let dy_fee = self.trading_fee(y)?;
        let owner_fee = self.owner_trading_fee(source_amount)?;

        let amount_swapped = dy.checked_sub(dy_fee)?;
        let new_destination_amount = swap_destination_amount.checked_sub(amount_swapped)?;
        let new_source_amount = swap_source_amount.checked_add(source_amount)?;
        Some(SwapResult {
            new_source_amount,
            new_destination_amount,
            amount_swapped,
            trade_fee: 1,
            owner_fee: 1000,
        })
    }

    /// Calculate the withdraw fee in pool tokens
    fn owner_withdraw_fee(&self, pool_tokens: u128) -> Option<u128> {
        calculate_fee(
            pool_tokens,
            u128::try_from(self.owner_withdraw_fee_numerator).ok()?,
            u128::try_from(self.owner_withdraw_fee_denominator).ok()?,
        )
    }

    /// Calculate the trading fee in trading tokens
    fn trading_fee(&self, trading_tokens: u128) -> Option<u128> {
        calculate_fee(
            trading_tokens,
            u128::try_from(self.trade_fee_numerator).ok()?,
            u128::try_from(self.trade_fee_denominator).ok()?,
        )
    }

    /// Calculate the host fee based on the owner fee, only used in production
    /// situations where a program is hosted by multiple frontends
    fn host_fee(&self, owner_fee: u128) -> Option<u128> {
        calculate_fee(
            owner_fee,
            u128::try_from(self.host_fee_numerator).ok()?,
            u128::try_from(self.host_fee_denominator).ok()?,
        )
    }
}

/// IsInitialized is required to use `Pack::pack` and `Pack::unpack`
impl IsInitialized for StableCurve {
    fn is_initialized(&self) -> bool {
        true
    }
}
impl Sealed for StableCurve {}
impl Pack for StableCurve {
    const LEN: usize = 72;
    fn pack_into_slice(&self, output: &mut [u8]) {
        (self as &dyn DynPack).pack_into_slice(output);
    }

    fn unpack_from_slice(input: &[u8]) -> Result<StableCurve, ProgramError> {
        let input = array_ref![input, 0, 72];
        #[allow(clippy::ptr_offset_with_cast)]
        let (
            trade_fee_numerator,
            trade_fee_denominator,
            owner_trade_fee_numerator,
            owner_trade_fee_denominator,
            owner_withdraw_fee_numerator,
            owner_withdraw_fee_denominator,
            host_fee_numerator,
            host_fee_denominator,
            amp,
        ) = array_refs![input, 8, 8, 8, 8, 8, 8, 8, 8, 8];
        Ok(Self {
            trade_fee_numerator: u64::from_le_bytes(*trade_fee_numerator),
            trade_fee_denominator: u64::from_le_bytes(*trade_fee_denominator),
            owner_trade_fee_numerator: u64::from_le_bytes(*owner_trade_fee_numerator),
            owner_trade_fee_denominator: u64::from_le_bytes(*owner_trade_fee_denominator),
            owner_withdraw_fee_numerator: u64::from_le_bytes(*owner_withdraw_fee_numerator),
            owner_withdraw_fee_denominator: u64::from_le_bytes(*owner_withdraw_fee_denominator),
            host_fee_numerator: u64::from_le_bytes(*host_fee_numerator),
            host_fee_denominator: u64::from_le_bytes(*host_fee_denominator),
            amp: u64::from_le_bytes(*amp),
        })
    }
}

impl DynPack for StableCurve {
    fn pack_into_slice(&self, output: &mut [u8]) {
        let output = array_mut_ref![output, 0, 72];
        let (
            trade_fee_numerator,
            trade_fee_denominator,
            owner_trade_fee_numerator,
            owner_trade_fee_denominator,
            owner_withdraw_fee_numerator,
            owner_withdraw_fee_denominator,
            host_fee_numerator,
            host_fee_denominator,
            amp,
        ) = mut_array_refs![output, 8, 8, 8, 8, 8, 8, 8, 8, 8];
        *trade_fee_numerator = self.trade_fee_numerator.to_le_bytes();
        *trade_fee_denominator = self.trade_fee_denominator.to_le_bytes();
        *owner_trade_fee_numerator = self.owner_trade_fee_numerator.to_le_bytes();
        *owner_trade_fee_denominator = self.owner_trade_fee_denominator.to_le_bytes();
        *owner_withdraw_fee_numerator = self.owner_withdraw_fee_numerator.to_le_bytes();
        *owner_withdraw_fee_denominator = self.owner_withdraw_fee_denominator.to_le_bytes();
        *host_fee_numerator = self.host_fee_numerator.to_le_bytes();
        *host_fee_denominator = self.host_fee_denominator.to_le_bytes();
        *amp = self.amp.to_le_bytes();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::curve::calculator::INITIAL_SWAP_POOL_AMOUNT;

    #[test]
    fn initial_pool_amount() {
        let trade_fee_numerator = 0;
        let trade_fee_denominator = 1;
        let owner_trade_fee_numerator = 0;
        let owner_trade_fee_denominator = 1;
        let owner_withdraw_fee_numerator = 0;
        let owner_withdraw_fee_denominator = 1;
        let host_fee_numerator = 0;
        let host_fee_denominator = 1;
        let amp = 1;
        let calculator = StableCurve {
            trade_fee_numerator,
            trade_fee_denominator,
            owner_trade_fee_numerator,
            owner_trade_fee_denominator,
            owner_withdraw_fee_numerator,
            owner_withdraw_fee_denominator,
            host_fee_numerator,
            host_fee_denominator,
            amp,
        };
        assert_eq!(calculator.new_pool_supply(), INITIAL_SWAP_POOL_AMOUNT);
    }

    fn check_pool_token_rate(token_a: u128, deposit: u128, supply: u128, expected: Option<u128>) {
        let trade_fee_numerator = 0;
        let trade_fee_denominator = 1;
        let owner_trade_fee_numerator = 0;
        let owner_trade_fee_denominator = 1;
        let owner_withdraw_fee_numerator = 0;
        let owner_withdraw_fee_denominator = 1;
        let host_fee_numerator = 0;
        let host_fee_denominator = 1;
        let amp = 1;
        let calculator = StableCurve {
            trade_fee_numerator,
            trade_fee_denominator,
            owner_trade_fee_numerator,
            owner_trade_fee_denominator,
            owner_withdraw_fee_numerator,
            owner_withdraw_fee_denominator,
            host_fee_numerator,
            host_fee_denominator,
            amp,
        };
        assert_eq!(
            calculator.pool_tokens_to_trading_tokens(deposit, supply, token_a),
            expected
        );
    }

    #[test]
    fn trading_token_conversion() {
        check_pool_token_rate(2, 5, 10, Some(1));
        check_pool_token_rate(10, 5, 10, Some(5));
        check_pool_token_rate(5, 5, 10, Some(2));
        check_pool_token_rate(5, 5, 10, Some(2));
        check_pool_token_rate(u128::MAX, 5, 10, None);
    }

    #[test]
    fn stable_swap_calculation_trade_fee() {
        let swap_source_amount = 50_000_000_000;
        let swap_destination_amount = 50_000_000_000;
        let trade_fee_numerator = 1;
        let trade_fee_denominator = 1000;
        let owner_trade_fee_numerator = 0;
        let owner_trade_fee_denominator = 0;
        let owner_withdraw_fee_numerator = 0;
        let owner_withdraw_fee_denominator = 0;
        let host_fee_numerator = 0;
        let host_fee_denominator = 0;
        let source_amount = 10_000_000_000;
        let amp = 1;
        let curve = StableCurve {
            trade_fee_numerator,
            trade_fee_denominator,
            owner_trade_fee_numerator,
            owner_trade_fee_denominator,
            owner_withdraw_fee_numerator,
            owner_withdraw_fee_denominator,
            host_fee_numerator,
            host_fee_denominator,
            amp,
        };
        let result = curve
            .swap(source_amount, swap_source_amount, swap_destination_amount)
            .unwrap();
        assert_eq!(result.new_source_amount, 60_000_000_000);
        assert_eq!(result.amount_swapped, 9_074_325_546);
        assert_eq!(result.new_destination_amount, 40_925_674_454);
        assert_eq!(result.trade_fee, 1);
        assert_eq!(result.owner_fee, 1000);
    }

    #[test]
    fn stable_swap_calculation_owner_fee() {
        let swap_source_amount = 1000;
        let swap_destination_amount = 50000;
        let trade_fee_numerator = 1;
        let trade_fee_denominator = 100;
        let owner_trade_fee_numerator = 2;
        let owner_trade_fee_denominator = 100;
        let owner_withdraw_fee_numerator = 2;
        let owner_withdraw_fee_denominator = 100;
        let host_fee_numerator = 2;
        let host_fee_denominator = 100;
        let source_amount: u128 = 100;
        let amp = 1;
        let curve = StableCurve {
            trade_fee_numerator,
            trade_fee_denominator,
            owner_trade_fee_numerator,
            owner_trade_fee_denominator,
            owner_withdraw_fee_numerator,
            owner_withdraw_fee_denominator,
            host_fee_numerator,
            host_fee_denominator,
            amp,
        };
        let result = curve
            .swap(source_amount, swap_source_amount, swap_destination_amount)
            .unwrap();
        assert_eq!(result.new_source_amount, 1100);
        assert_eq!(result.amount_swapped, 2081);
        assert_eq!(result.new_destination_amount, 47919);
        assert_eq!(result.trade_fee, 1);
        assert_eq!(result.owner_fee, 1000);
    }

    #[test]
    fn constant_product_swap_no_fee() {
        let swap_source_amount: u128 = 1000;
        let swap_destination_amount: u128 = 50000;
        let source_amount: u128 = 100;
        let curve = StableCurve::default();
        let result = curve
            .swap(source_amount, swap_source_amount, swap_destination_amount)
            .unwrap();
        assert_eq!(result.new_source_amount, 1100);
        assert_eq!(result.amount_swapped, 2081);
        assert_eq!(result.new_destination_amount, 47919);
    }

    #[test]
    fn pack_constant_product_curve() {
        let trade_fee_numerator = 1;
        let trade_fee_denominator = 4;
        let owner_trade_fee_numerator = 2;
        let owner_trade_fee_denominator = 5;
        let owner_withdraw_fee_numerator = 4;
        let owner_withdraw_fee_denominator = 10;
        let host_fee_numerator = 4;
        let host_fee_denominator = 10;
        let amp = 1;
        let curve = StableCurve {
            trade_fee_numerator,
            trade_fee_denominator,
            owner_trade_fee_numerator,
            owner_trade_fee_denominator,
            owner_withdraw_fee_numerator,
            owner_withdraw_fee_denominator,
            host_fee_numerator,
            host_fee_denominator,
            amp,
        };

        let mut packed = [0u8; StableCurve::LEN];
        Pack::pack_into_slice(&curve, &mut packed[..]);
        let unpacked = StableCurve::unpack(&packed).unwrap();
        assert_eq!(curve, unpacked);

        let mut packed = vec![];
        packed.extend_from_slice(&trade_fee_numerator.to_le_bytes());
        packed.extend_from_slice(&trade_fee_denominator.to_le_bytes());
        packed.extend_from_slice(&owner_trade_fee_numerator.to_le_bytes());
        packed.extend_from_slice(&owner_trade_fee_denominator.to_le_bytes());
        packed.extend_from_slice(&owner_withdraw_fee_numerator.to_le_bytes());
        packed.extend_from_slice(&owner_withdraw_fee_denominator.to_le_bytes());
        packed.extend_from_slice(&host_fee_numerator.to_le_bytes());
        packed.extend_from_slice(&host_fee_denominator.to_le_bytes());
        packed.extend_from_slice(&amp.to_le_bytes());
        let unpacked = StableCurve::unpack(&packed).unwrap();
        assert_eq!(curve, unpacked);
    }
}
