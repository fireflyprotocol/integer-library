# Integer Library

A formally verified library of common unsigned and signed operations.

# Specification Summary

This is a summary of Sui Prover formal verification results. To replicate the results:
1. Install Sui Prover
2. Run `sui-prover` in the `specs` directory
3. Run `sui-prover --no-bv-int-encoding` in the `specs-bv` directory

**✅ indicates that the specification is proved**

## `i128.move`

### `wrapping_add(num1: I128, num2: I128): I128`
 ✅ Computes `num1 + num2` with wrapping overflow.\
 ⏮️ The function does not abort.

### `shr(v: I128, shift: u8): I128`
 ✅ Computes arithmetic right shift `v >> shift`.\
 ⏮️ The function aborts unless `shift < 128`.


## `i32.move`

### `wrapping_add(num1: I32, num2: I32): I32`
 ✅ Computes `num1 + num2` with wrapping overflow.\
 ⏮️ The function does not abort.

### `shr(v: I32, shift: u8): I32`
 ✅ Computes arithmetic right shift `v >> shift`.\
 ⏮️ The function aborts unless `shift < 32`.


## `i64.move`

### `wrapping_add(num1: I64, num2: I64): I64`
 ✅ Computes `num1 + num2` with wrapping overflow.\
 ⏮️ The function does not abort.

### `shr(v: I64, shift: u8): I64`
 ✅ Computes arithmetic right shift `v >> shift`.\
 ⏮️ The function aborts unless `shift < 64`.


## `full_math_u128_specs.move`

### `full_mul(num1: u128, num2: u128): u256`
 ✅ Computes `num1 * num2` using 256-bit arithmetic for intermediate product computation.\
 ⏮️ The function does not abort.

### `mul_div_floor(num1: u128, num2: u128, denom: u128): u128`
 ✅ Computes `(num1 * num2) / denom` with floor division using 256-bit arithmetic for intermediate product computation.\
 ⏮️ The function aborts unless `denom > 0` and the result fits in `u128`.

### `mul_div_round(num1: u128, num2: u128, denom: u128): u128`
 ✅ Computes `(num1 * num2) / denom` with rounding division using 256-bit arithmetic for intermediate product computation.\
 ⏮️ The function aborts unless `denom > 0` and the result fits in `u128`.

### `mul_div_ceil(num1: u128, num2: u128, denom: u128): u128`
 ✅ Computes `(num1 * num2) / denom` with ceiling division using 256-bit arithmetic for intermediate product computation.\
 ⏮️ The function aborts unless `denom > 0` and the result fits in `u128`.

### `mul_shr(num1: u128, num2: u128, shift: u8): u128`
 ✅ Computes `(num1 * num2) >> shift` using 256-bit arithmetic for intermediate product computation.\
 ⏮️ The function aborts unless `shift <= 255` and the result fits in `u128`.

### `mul_shl(num1: u128, num2: u128, shift: u8): u128`
 ✅ Computes `(num1 * num2) << shift` using 256-bit arithmetic for intermediate product computation.\
 ⏮️ The function aborts unless `shift <= 255` and the result fits in `u128`.\
 ⚠️ Note that due to `<<` not aborting when losing significant bits, the actual result is `((num1 * num2) << shift) mod 2^256` (note the modulo), which can be unintuitive to users.


## `full_math_u64_specs.move`

### `full_mul(num1: u64, num2: u64): u128`
 ✅ Computes `num1 * num2` using 128-bit arithmetic for intermediate product computation.\
 ⏮️ The function does not abort.

### `mul_div_floor(num1: u64, num2: u64, denom: u64): u64`
 ✅ Computes `(num1 * num2) / denom` with floor division using 128-bit arithmetic for intermediate product computation.\
 ⏮️ The function aborts unless `denom > 0` and the result fits in `u64`.

### `mul_div_round(num1: u64, num2: u64, denom: u64): u64`
 ✅ Computes `(num1 * num2) / denom` with rounding division using 128-bit arithmetic for intermediate product computation.\
 ⏮️ The function aborts unless `denom > 0` and the result fits in `u64`.

### `mul_div_ceil(num1: u64, num2: u64, denom: u64): u64`
 ✅ Computes `(num1 * num2) / denom` with ceiling division using 128-bit arithmetic for intermediate product computation.\
 ⏮️ The function aborts unless `denom > 0` and the result fits in `u64`.

### `mul_shr(num1: u64, num2: u64, shift: u8): u64`
 ✅ Computes `(num1 * num2) >> shift` using 128-bit arithmetic for intermediate product computation.\
 ⏮️ The function aborts unless `shift <= 127` and the result fits in `u64`.

### `mul_shl(num1: u64, num2: u64, shift: u8): u64`
 ✅ Computes `(num1 * num2) << shift` using 128-bit arithmetic for intermediate product computation.\
 ⏮️ The function aborts unless `shift <= 127` and the result fits in `u64`.\
 ⚠️ Note that due to `<<` not aborting when losing significant bits, the actual result is `((num1 * num2) << shift) mod 2^128` (note the modulo), which can be unintuitive to users.


## `i128_specs.move`

### `zero(): I128`
 ✅ Computes `0` as an `I128`.\
 ⏮️ The function does not abort.

### `from(v: u128): I128`
 ✅ Computes an `I128` from a `u128`.\
 ⏮️ The function aborts when the value exceeds `I128::MAX`.

### `neg_from(v: u128): I128`
 ✅ Computes an `I128` from the negation of a `u128`.\
 ⏮️ The function aborts when the result does not fit in `I128`.

### `neg(v: I128): I128`
 ✅ Computes the negation of an `I128`.\
 ⏮️ The function aborts when the input is `MIN_I128`, that is `-2^127`.

### `wrapping_add(num1: I128, num2: I128): I128`
 ✅ Computes `num1 + num2` with wrapping overflow.\
 ⏮️ The function does not abort.\
 ⚠️ Proved in a separate package as it requires a custom prover configuration.

### `add(num1: I128, num2: I128): I128`
 ✅ Computes `num1 + num2`.\
 ⏮️ The function aborts when the result does not fit in `I128`.

### `overflowing_add(num1: I128, num2: I128): (I128, bool)`
 ✅ Computes `num1 + num2` and returns a flag indicating overflow.\
 ⏮️ The function does not abort.

### `wrapping_sub(num1: I128, num2: I128): I128`
 ✅ Computes `num1 - num2` with wrapping overflow.\
 ⏮️ The function does not abort.

### `sub(num1: I128, num2: I128): I128`
 ✅ Computes `num1 - num2`.\
 ⏮️ The function aborts when the result does not fit in `I128`.

### `overflowing_sub(num1: I128, num2: I128): (I128, bool)`
 ✅ Computes `num1 - num2` and returns a flag indicating overflow.\
 ⏮️ The function does not abort.

### `mul(num1: I128, num2: I128): I128`
 ✅ Computes `num1 * num2`.\
 ⏮️ The function aborts when the result does not fit in `I128`.

### `div(num1: I128, num2: I128): I128`
 ✅ Computes `num1 / num2` with truncation.\
 ⏮️ The function aborts when the result does not fit in `I128`, or the denominator is zero.

### `abs(v: I128): I128`
 ✅ Computes the absolute value of an `I128`.\
 ⏮️ The function aborts when the input is `MIN_I128`, that is `-2^127`.

### `abs_u128(v: I128): u128`
 ✅ Computes the absolute value of an `I128` as a `u128`.\
 ⏮️ The function does not abort.

### `shl(v: I128, shift: u8): I128`
 ✅ Computes `v << shift`.\
 ⏮️ The function aborts unless `shift < 128`.

### `shr(v: I128, shift: u8): I128`
 ✅ Computes `v >> shift`.\
 ⏮️ The function aborts unless `shift < 128`.\
 ⚠️ Proved in a separate package as it requires a custom prover configuration.

### `as_i64(v: I128): integer_mate::i64::I64`
 ✅ Converts an `I128` to an `I64`.\
 ⏮️ The function aborts when the value does not fit in `I64`.

### `as_i32(v: I128): integer_mate::i32::I32`
 ✅ Converts an `I128` to an `I32`.\
 ⏮️ The function aborts when the value does not fit in `I32`.

### `sign(v: I128): u8`
 ✅ Returns `1` if the input is negative, `0` otherwise.\
 ⏮️ The function does not abort.

### `is_neg(v: I128): bool`
 ✅ Returns `true` if the input is negative, `false` otherwise.\
 ⏮️ The function does not abort.

### `cmp(num1: I128, num2: I128): u8`
 ✅ Compares two `I128`s.\
 ⏮️ The function does not abort.

### `eq(num1: I128, num2: I128): bool`
 ✅ Compares two `I128`s, returns `true` if they are equal, `false` otherwise.\
 ⏮️ The function does not abort.

### `gt(num1: I128, num2: I128): bool`
 ✅ Compares two `I128`s, returns `true` if the first is greater than the second, `false` otherwise.\
 ⏮️ The function does not abort.

### `gte(num1: I128, num2: I128): bool`
 ✅ Compares two `I128`s, returns `true` if the first is greater than or equal to the second, `false` otherwise.\
 ⏮️ The function does not abort.

### `lt(num1: I128, num2: I128): bool`
 ✅ Compares two `I128`s, returns `true` if the first is less than the second, `false` otherwise.\
 ⏮️ The function does not abort.

### `lte(num1: I128, num2: I128): bool`
 ✅ Compares two `I128`s, returns `true` if the first is less than or equal to the second, `false` otherwise.\
 ⏮️ The function does not abort.

### `or(num1: I128, num2: I128): I128`
 ✅ Computes the bitwise OR of two `I128`s.\
 ⏮️ The function does not abort.

### `and(num1: I128, num2: I128): I128`
 ✅ Computes the bitwise AND of two `I128`s.\
 ⏮️ The function does not abort.

### `u128_neg(v: u128): u128`
 ✅ Computes the bitwise NOT of a `u128`.\
 ⏮️ The function does not abort.

### `u8_neg(v: u8): u8`
 ✅ Computes the bitwise NOT of a `u8`.\
 ⏮️ The function does not abort.


## `i32_specs.move`

### `zero(): I32`
 ✅ Computes `0` as an `I32`.\
 ⏮️ The function does not abort.

### `from_u32(v: u32): I32`
 ✅ Computes an `I32` from a `u32`.\
 ⏮️ The function does not abort.

### `from(v: u32): I32`
 ✅ Computes an `I32` from a `u32`.\
 ⏮️ The function does not abort.

### `neg_from(v: u32): I32`
 ✅ Computes an `I32` from a `u32`.\
 ⏮️ The function aborts when the result does not fit in `I32`.

### `wrapping_add(num1: I32, num2: I32): I32`
 ✅ Computes `num1 + num2` with wrapping overflow.\
 ⏮️ The function does not abort.\
 ⚠️ Proved in a separate package as it requires a custom prover configuration.

### `add(num1: I32, num2: I32): I32`
 ✅ Computes `num1 + num2`.\
 ⏮️ The function aborts when the result does not fit in `I32`.

### `wrapping_sub(num1: I32, num2: I32): I32`
 ✅ Computes `num1 - num2` with wrapping overflow.\
 ⏮️ The function does not abort.

### `sub(num1: I32, num2: I32): I32`
 ✅ Computes `num1 - num2`.\
 ⏮️ The function aborts when the result does not fit in `I32`.\
 ⚠️ This function was initially incorrect but fixed after our reporting. Replace the target with `sub_buggy` to see the how the bug is caught.

### `mul(num1: I32, num2: I32): I32`
 ✅ Computes `num1 * num2`.\
 ⏮️ The function aborts when the result does not fit in `I32`.

### `div(num1: I32, num2: I32): I32`
 ✅ Computes `num1 / num2` with truncation.\
 ⏮️ The function aborts when the result does not fit in `I32`, or the denominator is zero.

### `abs(v: I32): I32`
 ✅ Computes the absolute value of an `I32`.\
 ⏮️ The function aborts when the input is `MIN_I32`, that is `-2^31`.

### `abs_u32(v: I32): u32`
 ✅ Computes the absolute value of an `I32` as a `u32`.\
 ⏮️ The function does not abort.

### `shl(v: I32, shift: u8): I32`
 ✅ Computes `v << shift`.\
 ⏮️ The function aborts unless `shift < 32`.

### `shr(v: I32, shift: u8): I32`
 ✅ Computes `v >> shift`.\
 ⏮️ The function aborts unless `shift < 32`.\
 ⚠️ Proved in a separate package as it requires a custom prover configuration.

### `mod(v: I32, n: I32): I32`
 ✅ Computes `v % n`.\
 ⏮️ The function aborts when the denominator is zero.

### `sign(v: I32): u8`
 ✅ Returns `1` if the input is negative, `0` otherwise.\
 ⏮️ The function does not abort.

### `is_neg(v: I32): bool`
 ✅ Returns `true` if the input is negative, `false` otherwise.\
 ⏮️ The function does not abort.

### `cmp(num1: I32, num2: I32): u8`
 ✅ Compares two `I32`s.\
 ⏮️ The function does not abort.

### `eq(num1: I32, num2: I32): bool`
 ✅ Compares two `I32`s, returns `true` if they are equal, `false` otherwise.\
 ⏮️ The function does not abort.

### `gt(num1: I32, num2: I32): bool`
 ✅ Compares two `I32`s, returns `true` if the first is greater than the second, `false` otherwise.\
 ⏮️ The function does not abort.

### `gte(num1: I32, num2: I32): bool`
 ✅ Compares two `I32`s, returns `true` if the first is greater than or equal to the second, `false` otherwise.\
 ⏮️ The function does not abort.

### `lt(num1: I32, num2: I32): bool`
 ✅ Compares two `I32`s, returns `true` if the first is less than the second, `false` otherwise.\
 ⏮️ The function does not abort.

### `lte(num1: I32, num2: I32): bool`
 ✅ Compares two `I32`s, returns `true` if the first is less than or equal to the second, `false` otherwise.\
 ⏮️ The function does not abort.

### `or(num1: I32, num2: I32): I32`
 ✅ Computes the bitwise OR of two `I32`s.\
 ⏮️ The function does not abort.

### `and(num1: I32, num2: I32): I32`
 ✅ Computes the bitwise AND of two `I32`s.\
 ⏮️ The function does not abort.

### `u32_neg(v: u32): u32`
 ✅ Computes the bitwise NOT of a `u32`.\
 ⏮️ The function does not abort.

### `u8_neg(v: u8): u8`
 ✅ Computes the bitwise NOT of a `u8`.\
 ⏮️ The function does not abort.


## `i64_specs.move`

### `zero(): I64`
 ✅ Computes `0` as an `I64`.\
 ⏮️ The function does not abort.

### `from_u64(v: u64): I64`
 ✅ Computes an `I64` from a `u64`.\
 ⏮️ The function does not abort.

### `from(v: u64): I64`
 ✅ Computes an `I64` from a `u64`.\
 ⏮️ The function does not abort.

### `neg_from(v: u64): I64`
 ✅ Computes an `I64` from a `u64`.\
 ⏮️ The function aborts when the result does not fit in `I64`.

### `wrapping_add(num1: I64, num2: I64): I64`
 ✅ Computes `num1 + num2` with wrapping overflow.\
 ⏮️ The function does not abort.\
 ⚠️ Proved in a separate package as it requires a custom prover configuration.

### `add(num1: I64, num2: I64): I64`
 ✅ Computes `num1 + num2`.\
 ⏮️ The function aborts when the result does not fit in `I64`.

### `wrapping_sub(num1: I64, num2: I64): I64`
 ✅ Computes `num1 - num2` with wrapping overflow.\
 ⏮️ The function does not abort.

### `sub(num1: I64, num2: I64): I64`
 ✅ Computes `num1 - num2`.\
 ⏮️ The function aborts when the result does not fit in `I64`.

### `mul(num1: I64, num2: I64): I64`
 ✅ Computes `num1 * num2`.\
 ⏮️ The function aborts when the result does not fit in `I64`.

### `div(num1: I64, num2: I64): I64`
 ✅ Computes `num1 / num2` with truncation.\
 ⏮️ The function aborts when the result does not fit in `I64`, or the denominator is zero.

### `abs(v: I64): I64`
 ✅ Computes the absolute value of an `I64`.\
 ⏮️ The function aborts when the input is `MIN_I64`, that is `-2^63`.

### `abs_u64(v: I64): u64`
 ✅ Computes the absolute value of an `I64` as a `u64`.\
 ⏮️ The function does not abort.

### `shl(v: I64, shift: u8): I64`
 ✅ Computes `v << shift`.\
 ⏮️ The function aborts unless `shift < 64`.

### `shr(v: I64, shift: u8): I64`
 ✅ Computes `v >> shift`.\
 ⏮️ The function aborts unless `shift < 64`.\
 ⚠️ Proved in a separate package as it requires a custom prover configuration.

### `mod(v: I64, n: I64): I64`
 ✅ Computes `v % n`.\
 ⏮️ The function aborts when the denominator is zero.

### `sign(v: I64): u8`
 ✅ Returns `1` if the input is negative, `0` otherwise.\
 ⏮️ The function does not abort.

### `is_neg(v: I64): bool`
 ✅ Returns `true` if the input is negative, `false` otherwise.\
 ⏮️ The function does not abort.

### `cmp(num1: I64, num2: I64): u8`
 ✅ Compares two `I64`s.\
 ⏮️ The function does not abort.

### `eq(num1: I64, num2: I64): bool`
 ✅ Compares two `I64`s, returns `true` if they are equal, `false` otherwise.\
 ⏮️ The function does not abort.

### `gt(num1: I64, num2: I64): bool`
 ✅ Compares two `I64`s, returns `true` if the first is greater than the second, `false` otherwise.\
 ⏮️ The function does not abort.

### `gte(num1: I64, num2: I64): bool`
 ✅ Compares two `I64`s, returns `true` if the first is greater than or equal to the second, `false` otherwise.\
 ⏮️ The function does not abort.

### `lt(num1: I64, num2: I64): bool`
 ✅ Compares two `I64`s, returns `true` if the first is less than the second, `false` otherwise.\
 ⏮️ The function does not abort.

### `lte(num1: I64, num2: I64): bool`
 ✅ Compares two `I64`s, returns `true` if the first is less than or equal to the second, `false` otherwise.\
 ⏮️ The function does not abort.

### `or(num1: I64, num2: I64): I64`
 ✅ Computes the bitwise OR of two `I64`s.\
 ⏮️ The function does not abort.

### `and(num1: I64, num2: I64): I64`
 ✅ Computes the bitwise AND of two `I64`s.\
 ⏮️ The function does not abort.

### `u64_neg(v: u64): u64`
 ✅ Computes the bitwise NOT of a `u64`.\
 ⏮️ The function does not abort.

### `u8_neg(v: u8): u8`
 ✅ Computes the bitwise NOT of a `u8`.\
 ⏮️ The function does not abort.


## `math_u128_specs.move`

### `wrapping_add(n1: u128, n2: u128): u128`
 ✅ Computes `n1 + n2` with wrapping overflow.\
 ⏮️ The function does not abort.

### `overflowing_add(n1: u128, n2: u128): (u128, bool)`
 ✅ Computes `n1 + n2` with wrapping overflow and a boolean indicating overflow.\
 ⏮️ The function does not abort.

### `wrapping_sub(n1: u128, n2: u128): u128`
 ✅ Computes `n1 - n2` with wrapping overflow.\
 ⏮️ The function does not abort.

### `overflowing_sub(n1: u128, n2: u128): (u128, bool)`
 ✅ Computes `n1 - n2` with wrapping overflow and a boolean indicating overflow.\
 ⏮️ The function does not abort.

### `wrapping_mul(n1: u128, n2: u128): u128`
 ✅ Computes `n1 * n2` with wrapping overflow.\
 ⏮️ The function does not abort.

### `overflowing_mul(n1: u128, n2: u128): (u128, bool)`
 ✅ Computes `n1 * n2` with wrapping overflow and a boolean indicating overflow.\
 ⏮️ The function does not abort.

### `full_mul(n1: u128, n2: u128): (u128, u128)`
 ✅ Computes the full 256-bit product of `n1 * n2` as two u128 values (lo, hi).\
 ⏮️ The function does not abort.

### `hi(n: u128): u64`
 ✅ Extracts the high 64 bits of a u128 value.\
 ⏮️ The function does not abort.

### `lo(n: u128): u64`
 ✅ Extracts the low 64 bits of a u128 value.\
 ⏮️ The function does not abort.

### `hi_u128(n: u128): u128`
 ✅ Extracts the high 64 bits of a u128 value as a u128.\
 ⏮️ The function does not abort.

### `lo_u128(n: u128): u128`
 ✅ Extracts the low 64 bits of a u128 value as a u128.\
 ⏮️ The function does not abort.

### `from_lo_hi(lo: u64, hi: u64): u128`
 ✅ Constructs a u128 from low and high u64 components.\
 ⏮️ The function does not abort.

### `checked_div_round(num: u128, denom: u128, round_up: bool): u128`
 ✅ Computes `num / denom` with optional rounding up.\
 ⏮️ The function aborts if `denom == 0`.

### `max(num1: u128, num2: u128): u128`
 ✅ Returns the maximum of two u128 values.\
 ⏮️ The function does not abort.

### `min(num1: u128, num2: u128): u128`
 ✅ Returns the minimum of two u128 values.\
 ⏮️ The function does not abort.

### `add_check(num1: u128, num2: u128): bool`
 ✅ Checks if `num1 + num2` will overflow.\
 ⏮️ The function does not abort.


## `math_u256_specs.move`

### `div_mod(num: u256, denom: u256): (u256, u256)`
 ✅ Computes `num / denom` and `num % denom`.\
 ⏮️ The function aborts if `denom == 0`.

### `shlw(n: u256): u256`
 ✅ Shifts `n` left by 64 bits (one word) with wrapping overflow.\
 ⏮️ The function does not abort.

### `shrw(n: u256): u256`
 ✅ Shifts `n` right by 64 bits (one word).\
 ⏮️ The function does not abort.

### `checked_shlw(n: u256): (u256, bool)`
 ✅ Shifts `n` left by 64 bits (one word) and returns a boolean indicating overflow.\
 ⏮️ The function does not abort.\
 ⚠️ Returns (0, true) when overflow occurs, not the wrapped value.

### `div_round(num: u256, denom: u256, round_up: bool): u256`
 ✅ Computes `num / denom` with optional rounding up.\
 ⏮️ The function aborts if `denom == 0`.

### `add_check(num1: u256, num2: u256): bool`
 ✅ Checks if `num1 + num2` will overflow.\
 ⏮️ The function does not abort.


## `math_u64_specs.move`

### `wrapping_add(n1: u64, n2: u64): u64`
 ✅ Computes `n1 + n2` with wrapping overflow.\
 ⏮️ The function does not abort.

### `overflowing_add(n1: u64, n2: u64): (u64, bool)`
 ✅ Computes `n1 + n2` with wrapping overflow and a boolean indicating overflow.\
 ⏮️ The function does not abort.

### `wrapping_sub(n1: u64, n2: u64): u64`
 ✅ Computes `n1 - n2` with wrapping overflow.\
 ⏮️ The function does not abort.

### `overflowing_sub(n1: u64, n2: u64): (u64, bool)`
 ✅ Computes `n1 - n2` with wrapping overflow and a boolean indicating overflow.\
 ⏮️ The function does not abort.

### `wrapping_mul(n1: u64, n2: u64): u64`
 ✅ Computes `n1 * n2` with wrapping overflow.\
 ⏮️ The function does not abort.

### `overflowing_mul(n1: u64, n2: u64): (u64, bool)`
 ✅ Computes `n1 * n2` with overflowing overflow and a boolean indicating overflow.\
 ⏮️ The function does not abort.

### `carry_add(n1: u64, n2: u64, carry: u64): (u64, u64)`
 ✅ Computes `n1 + n2 + carry` returning the result and the new carry.\
 ⏮️ The function aborts unless `carry <= 1`.

### `add_check(n1: u64, n2: u64): bool`
 ✅ Checks if `n1 + n2` will overflow.\
 ⏮️ The function does not abort.

