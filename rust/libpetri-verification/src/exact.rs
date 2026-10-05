//! Exact integers of unbounded size and exact rationals over them, for the colour-slot
//! linear program of [NU-053] ([`crate::slot_bound_lp`]).
//!
//! The slot bound must come out the same in every implementation, so its simplex and
//! its checker compute exactly: no floating point, and no fixed-width arithmetic that
//! refuses on overflow (Java's `BigInteger` and TypeScript's `bigint` could not refuse
//! at the same points). This module is the Rust side of that arithmetic. It keeps the
//! crate free of third-party dependencies and offers only what the slot bound uses:
//! addition, subtraction, multiplication, truncating division with remainder, gcd,
//! comparison and decimal display.
//!
//! A value that fits an `i64` is stored as one, and every operation on two such values
//! first tries the checked `i64` operation. Only a result that does not fit moves to the
//! limb representation, so the common case allocates nothing. [`Rational`] does the same
//! one level up: when both operands' parts fit an `i64`, it forms the cross products in
//! `i128` and reduces them there. Both representations
//! hold exactly the same set of values and a value has one representation (a limb
//! number never fits an `i64`), so equality and hashing are structural.

use std::cmp::Ordering;
use std::fmt;

/// An integer of unbounded size.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BigInt(Repr);

#[derive(Clone, PartialEq, Eq, Hash)]
enum Repr {
    /// Every value that fits an `i64`.
    Small(i64),
    /// Every other value: a sign and a little-endian magnitude of 32-bit limbs with no
    /// leading zero limb. The magnitude never fits an `i64` of that sign.
    Large { neg: bool, mag: Vec<u32> },
}

impl BigInt {
    pub fn zero() -> Self {
        BigInt(Repr::Small(0))
    }

    pub fn one() -> Self {
        BigInt(Repr::Small(1))
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.0, Repr::Small(0))
    }

    pub fn is_negative(&self) -> bool {
        match &self.0 {
            Repr::Small(v) => *v < 0,
            Repr::Large { neg, .. } => *neg,
        }
    }

    pub fn is_positive(&self) -> bool {
        !self.is_negative() && !self.is_zero()
    }

    /// The value as an `i64`, when it fits.
    pub fn to_i64(&self) -> Option<i64> {
        match &self.0 {
            Repr::Small(v) => Some(*v),
            Repr::Large { .. } => None,
        }
    }

    pub fn abs(&self) -> BigInt {
        if self.is_negative() { -self } else { self.clone() }
    }

    /// Sign and magnitude, whatever the representation.
    fn parts(&self) -> (bool, Vec<u32>) {
        match &self.0 {
            Repr::Small(v) => (*v < 0, mag_from_u64(v.unsigned_abs())),
            Repr::Large { neg, mag } => (*neg, mag.clone()),
        }
    }

    /// The value with this sign and magnitude, in its one representation.
    fn from_parts(neg: bool, mut mag: Vec<u32>) -> BigInt {
        trim(&mut mag);
        if mag.len() <= 2 {
            let v = mag_to_u64(&mag);
            if !neg && v <= i64::MAX as u64 {
                return BigInt(Repr::Small(v as i64));
            }
            if neg && v <= 1u64 << 63 {
                return BigInt(Repr::Small((v as i64).wrapping_neg()));
            }
        }
        BigInt(Repr::Large { neg, mag })
    }

    /// Truncating division with remainder: `self = q·d + r`, `|r| < |d|`, `r` with the
    /// sign of `self` (or zero). Panics when `d` is zero.
    pub fn div_rem(&self, d: &BigInt) -> (BigInt, BigInt) {
        assert!(!d.is_zero(), "BigInt division by zero");
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &d.0) {
            if let (Some(q), Some(r)) = (a.checked_div(*b), a.checked_rem(*b)) {
                return (BigInt(Repr::Small(q)), BigInt(Repr::Small(r)));
            }
        }
        let (an, am) = self.parts();
        let (dn, dm) = d.parts();
        let (q, r) = mag_div_rem(&am, &dm);
        (BigInt::from_parts(an != dn, q), BigInt::from_parts(an, r))
    }

    /// The greatest common divisor, never negative; `gcd(0, 0) = 0`.
    pub fn gcd(&self, other: &BigInt) -> BigInt {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0) {
            return BigInt::from(gcd_u64(a.unsigned_abs(), b.unsigned_abs()));
        }
        let mut a = self.abs();
        let mut b = other.abs();
        while !b.is_zero() {
            if let (Repr::Small(x), Repr::Small(y)) = (&a.0, &b.0) {
                return BigInt::from(gcd_u64(x.unsigned_abs(), y.unsigned_abs()));
            }
            let r = a.div_rem(&b).1;
            a = b;
            b = r;
        }
        a
    }
}

impl From<i64> for BigInt {
    fn from(v: i64) -> Self {
        BigInt(Repr::Small(v))
    }
}

impl From<u64> for BigInt {
    fn from(v: u64) -> Self {
        BigInt::from_parts(false, mag_from_u64(v))
    }
}

impl From<usize> for BigInt {
    fn from(v: usize) -> Self {
        BigInt::from(v as u64)
    }
}

impl From<i128> for BigInt {
    fn from(v: i128) -> Self {
        let m = v.unsigned_abs();
        let mag = vec![m as u32, (m >> 32) as u32, (m >> 64) as u32, (m >> 96) as u32];
        BigInt::from_parts(v < 0, mag)
    }
}

impl Ord for BigInt {
    fn cmp(&self, other: &Self) -> Ordering {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0) {
            return a.cmp(b);
        }
        let (an, am) = self.parts();
        let (bn, bm) = other.parts();
        match (an, bn) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            (false, false) => mag_cmp(&am, &bm),
            (true, true) => mag_cmp(&bm, &am),
        }
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl std::ops::Neg for &BigInt {
    type Output = BigInt;
    fn neg(self) -> BigInt {
        match &self.0 {
            Repr::Small(v) => match v.checked_neg() {
                Some(n) => BigInt(Repr::Small(n)),
                None => BigInt::from_parts(false, mag_from_u64(v.unsigned_abs())),
            },
            Repr::Large { neg, mag } => BigInt::from_parts(!neg, mag.clone()),
        }
    }
}

impl std::ops::Neg for BigInt {
    type Output = BigInt;
    fn neg(self) -> BigInt {
        -&self
    }
}

/// Signed sum of two sign-magnitude values.
fn add_parts(an: bool, am: &[u32], bn: bool, bm: &[u32]) -> BigInt {
    if an == bn {
        return BigInt::from_parts(an, mag_add(am, bm));
    }
    match mag_cmp(am, bm) {
        Ordering::Equal => BigInt::zero(),
        Ordering::Greater => BigInt::from_parts(an, mag_sub(am, bm)),
        Ordering::Less => BigInt::from_parts(bn, mag_sub(bm, am)),
    }
}

impl std::ops::Add for &BigInt {
    type Output = BigInt;
    fn add(self, rhs: &BigInt) -> BigInt {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0) {
            if let Some(s) = a.checked_add(*b) {
                return BigInt(Repr::Small(s));
            }
        }
        let (an, am) = self.parts();
        let (bn, bm) = rhs.parts();
        add_parts(an, &am, bn, &bm)
    }
}

impl std::ops::Sub for &BigInt {
    type Output = BigInt;
    fn sub(self, rhs: &BigInt) -> BigInt {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0) {
            if let Some(s) = a.checked_sub(*b) {
                return BigInt(Repr::Small(s));
            }
        }
        let (an, am) = self.parts();
        let (bn, bm) = rhs.parts();
        add_parts(an, &am, !bn, &bm)
    }
}

impl std::ops::Mul for &BigInt {
    type Output = BigInt;
    fn mul(self, rhs: &BigInt) -> BigInt {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0) {
            if let Some(p) = a.checked_mul(*b) {
                return BigInt(Repr::Small(p));
            }
        }
        let (an, am) = self.parts();
        let (bn, bm) = rhs.parts();
        BigInt::from_parts(an != bn, mag_mul(&am, &bm))
    }
}

impl fmt::Display for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Repr::Small(v) => write!(f, "{v}"),
            Repr::Large { neg, mag } => {
                // Base 10^9 digits, least significant first.
                let mut chunks: Vec<u32> = Vec::new();
                let mut rest = mag.clone();
                while !rest.is_empty() {
                    let (q, r) = mag_div_small(&rest, 1_000_000_000);
                    chunks.push(r);
                    rest = q;
                }
                if *neg {
                    f.write_str("-")?;
                }
                let mut iter = chunks.iter().rev();
                if let Some(first) = iter.next() {
                    write!(f, "{first}")?;
                }
                for c in iter {
                    write!(f, "{c:09}")?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Debug for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

// ---- magnitudes: little-endian u32 limbs ----

fn trim(mag: &mut Vec<u32>) {
    while mag.last() == Some(&0) {
        mag.pop();
    }
}

fn mag_from_u64(v: u64) -> Vec<u32> {
    let mut mag = vec![v as u32, (v >> 32) as u32];
    trim(&mut mag);
    mag
}

/// The value of a magnitude of at most two limbs.
fn mag_to_u64(mag: &[u32]) -> u64 {
    mag.iter().rev().fold(0u64, |acc, &l| (acc << 32) | l as u64)
}

fn mag_cmp(a: &[u32], b: &[u32]) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| a.iter().rev().cmp(b.iter().rev()))
}

fn mag_add(a: &[u32], b: &[u32]) -> Vec<u32> {
    let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let mut out = Vec::with_capacity(long.len() + 1);
    let mut carry = 0u64;
    for (i, &x) in long.iter().enumerate() {
        let s = x as u64 + short.get(i).copied().unwrap_or(0) as u64 + carry;
        out.push(s as u32);
        carry = s >> 32;
    }
    if carry != 0 {
        out.push(carry as u32);
    }
    out
}

/// `a - b` for `a ≥ b`.
fn mag_sub(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len());
    let mut borrow = 0i64;
    for (i, &x) in a.iter().enumerate() {
        let mut d = x as i64 - b.get(i).copied().unwrap_or(0) as i64 - borrow;
        if d < 0 {
            d += 1i64 << 32;
            borrow = 1;
        } else {
            borrow = 0;
        }
        out.push(d as u32);
    }
    debug_assert_eq!(borrow, 0, "mag_sub needs a >= b");
    trim(&mut out);
    out
}

fn mag_mul(a: &[u32], b: &[u32]) -> Vec<u32> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![0u32; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        let mut carry = 0u64;
        for (j, &y) in b.iter().enumerate() {
            let t = x as u64 * y as u64 + out[i + j] as u64 + carry;
            out[i + j] = t as u32;
            carry = t >> 32;
        }
        out[i + b.len()] = carry as u32;
    }
    trim(&mut out);
    out
}

/// Division of a magnitude by one non-zero limb.
fn mag_div_small(a: &[u32], d: u32) -> (Vec<u32>, u32) {
    let mut q = vec![0u32; a.len()];
    let mut r = 0u64;
    for i in (0..a.len()).rev() {
        let cur = (r << 32) | a[i] as u64;
        q[i] = (cur / d as u64) as u32;
        r = cur % d as u64;
    }
    trim(&mut q);
    (q, r as u32)
}

fn shl_bits(a: &[u32], s: u32, extra: bool) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len() + 1);
    if s == 0 {
        out.extend_from_slice(a);
        if extra {
            out.push(0);
        }
        return out;
    }
    let mut carry = 0u32;
    for &x in a {
        out.push((x << s) | carry);
        carry = x >> (32 - s);
    }
    if extra {
        out.push(carry);
    }
    out
}

/// Long division of magnitudes (Knuth, TAOCP vol. 2, 4.3.1, Algorithm D, in the form of
/// Warren's `divmnu`). `d` is non-empty.
fn mag_div_rem(a: &[u32], d: &[u32]) -> (Vec<u32>, Vec<u32>) {
    if mag_cmp(a, d) == Ordering::Less {
        return (Vec::new(), a.to_vec());
    }
    if d.len() == 1 {
        let (q, r) = mag_div_small(a, d[0]);
        let mut r = vec![r];
        trim(&mut r);
        return (q, r);
    }
    let n = d.len();
    let m = a.len();
    let s = d[n - 1].leading_zeros();
    let vn = shl_bits(d, s, false);
    let mut un = shl_bits(a, s, true);
    let mut q = vec![0u32; m - n + 1];
    const B: u64 = 1 << 32;
    for j in (0..=m - n).rev() {
        let num = ((un[j + n] as u64) << 32) | un[j + n - 1] as u64;
        let mut qhat = num / vn[n - 1] as u64;
        let mut rhat = num % vn[n - 1] as u64;
        while qhat >= B
            || (qhat as u128) * (vn[n - 2] as u128) > ((rhat as u128) << 32) + un[j + n - 2] as u128
        {
            qhat -= 1;
            rhat += vn[n - 1] as u64;
            if rhat >= B {
                break;
            }
        }
        // Multiply and subtract.
        let mut k: i64 = 0;
        for i in 0..n {
            let p = qhat * vn[i] as u64;
            let t = un[i + j] as i64 - k - (p & 0xFFFF_FFFF) as i64;
            un[i + j] = t as u32;
            k = (p >> 32) as i64 - (t >> 32);
        }
        let t = un[j + n] as i64 - k;
        un[j + n] = t as u32;
        if t < 0 {
            // Subtracted one time too many: add back.
            qhat -= 1;
            let mut carry = 0u64;
            for i in 0..n {
                let s2 = un[i + j] as u64 + vn[i] as u64 + carry;
                un[i + j] = s2 as u32;
                carry = s2 >> 32;
            }
            un[j + n] = un[j + n].wrapping_add(carry as u32);
        }
        q[j] = qhat as u32;
    }
    // Unnormalise the remainder.
    let mut r = vec![0u32; n];
    for i in 0..n {
        r[i] = if s == 0 { un[i] } else { (un[i] >> s) | (un[i + 1] << (32 - s)) };
    }
    trim(&mut q);
    trim(&mut r);
    (q, r)
}

/// Binary GCD: `u128` division is a software routine, so Euclid's remainders cost more
/// than shifts and subtractions.
fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    if a == 0 || b == 0 {
        return a | b;
    }
    let shift = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b {
            (a, b) = (b, a);
        }
        b -= a;
        if b == 0 {
            return a << shift;
        }
    }
}

fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

/// An exact rational number in lowest terms with a positive denominator.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Rational {
    num: BigInt,
    den: BigInt,
}

impl Rational {
    pub fn zero() -> Self {
        Rational { num: BigInt::zero(), den: BigInt::one() }
    }

    pub fn from_int(v: BigInt) -> Self {
        Rational { num: v, den: BigInt::one() }
    }

    /// `num / den` in lowest terms. Panics when `den` is zero.
    pub fn new(num: BigInt, den: BigInt) -> Self {
        assert!(!den.is_zero(), "Rational with a zero denominator");
        let g = num.gcd(&den);
        let (mut num, mut den) = if g == BigInt::one() {
            (num, den)
        } else {
            (num.div_rem(&g).0, den.div_rem(&g).0)
        };
        if den.is_negative() {
            num = -num;
            den = -den;
        }
        Rational { num, den }
    }

    pub fn numer(&self) -> &BigInt {
        &self.num
    }

    pub fn denom(&self) -> &BigInt {
        &self.den
    }

    pub fn is_zero(&self) -> bool {
        self.num.is_zero()
    }

    pub fn is_negative(&self) -> bool {
        self.num.is_negative()
    }

    pub fn is_positive(&self) -> bool {
        self.num.is_positive()
    }

    /// Numerators and denominators of both operands, when all four fit in `i64`.
    fn small(&self, o: &Rational) -> Option<[i128; 4]> {
        Some([
            self.num.to_i64()? as i128,
            self.den.to_i64()? as i128,
            o.num.to_i64()? as i128,
            o.den.to_i64()? as i128,
        ])
    }

    /// `num / den` in lowest terms from `i128` parts; `None` when `den` is zero. The fast
    /// path of the arithmetic below, which keeps operands that fit in `i64` off the
    /// limb representation.
    fn from_i128(num: i128, den: i128) -> Option<Self> {
        if den == 0 {
            return None;
        }
        let g = gcd_u128(num.unsigned_abs(), den.unsigned_abs()) as i128;
        let (num, den) = (num / g, den / g);
        let (num, den) = if den < 0 { (num.checked_neg()?, -den) } else { (num, den) };
        Some(Rational { num: BigInt::from(num), den: BigInt::from(den) })
    }

    pub fn add(&self, o: &Rational) -> Rational {
        if let Some([a, b, c, d]) = self.small(o)
            && let Some(r) = (a * d).checked_add(c * b).and_then(|n| Rational::from_i128(n, b * d))
        {
            return r;
        }
        if self.den == o.den {
            return Rational::new(&self.num + &o.num, self.den.clone());
        }
        Rational::new(&(&self.num * &o.den) + &(&o.num * &self.den), &self.den * &o.den)
    }

    pub fn sub(&self, o: &Rational) -> Rational {
        if let Some([a, b, c, d]) = self.small(o)
            && let Some(r) = (a * d).checked_sub(c * b).and_then(|n| Rational::from_i128(n, b * d))
        {
            return r;
        }
        if self.den == o.den {
            return Rational::new(&self.num - &o.num, self.den.clone());
        }
        Rational::new(&(&self.num * &o.den) - &(&o.num * &self.den), &self.den * &o.den)
    }

    pub fn mul(&self, o: &Rational) -> Rational {
        if let Some([a, b, c, d]) = self.small(o)
            && let Some(r) = Rational::from_i128(a * c, b * d)
        {
            return r;
        }
        Rational::new(&self.num * &o.num, &self.den * &o.den)
    }

    /// Panics when `o` is zero.
    pub fn div(&self, o: &Rational) -> Rational {
        if let Some([a, b, c, d]) = self.small(o)
            && c != 0
            && let Some(r) = Rational::from_i128(a * d, b * c)
        {
            return r;
        }
        Rational::new(&self.num * &o.den, &self.den * &o.num)
    }

    pub fn neg(&self) -> Rational {
        Rational { num: -&self.num, den: self.den.clone() }
    }
}

impl From<i64> for Rational {
    fn from(v: i64) -> Self {
        Rational::from_int(BigInt::from(v))
    }
}

impl Ord for Rational {
    fn cmp(&self, o: &Self) -> Ordering {
        if self.den == o.den {
            return self.num.cmp(&o.num);
        }
        (&self.num * &o.den).cmp(&(&o.num * &self.den))
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// `6` for an integer, `14/3` otherwise.
impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den == BigInt::one() {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

impl fmt::Debug for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// xorshift64*, so the property tests need no dependency.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        /// An i128 of a random bit length, so every limb count from 0 to 4 occurs.
        fn i128(&mut self) -> i128 {
            let v = ((self.next() as u128) << 64 | self.next() as u128) >> (self.next() % 128);
            if self.next() % 2 == 0 { v as i128 } else { (v as i128).wrapping_neg() }
        }
        fn big(&mut self, limbs: usize) -> BigInt {
            let mag: Vec<u32> = (0..limbs).map(|_| self.next() as u32).collect();
            BigInt::from_parts(self.next() % 2 == 0, mag)
        }
    }

    #[test]
    fn arithmetic_agrees_with_i128_on_values_up_to_four_limbs() {
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        for _ in 0..20_000 {
            let (a, b) = (rng.i128() >> 2, rng.i128() >> 2);
            let (x, y) = (BigInt::from(a), BigInt::from(b));
            assert_eq!(&x + &y, BigInt::from(a + b), "{a} + {b}");
            assert_eq!(&x - &y, BigInt::from(a - b), "{a} - {b}");
            assert_eq!(x.cmp(&y), a.cmp(&b), "{a} <=> {b}");
            assert_eq!(x.to_string(), a.to_string());
            if let Some(p) = (a >> 64).checked_mul(b >> 64) {
                let (a, b) = (a >> 64, b >> 64);
                assert_eq!(&BigInt::from(a) * &BigInt::from(b), BigInt::from(p), "{a} * {b}");
            }
            if b != 0 {
                let (q, r) = x.div_rem(&y);
                assert_eq!((q, r), (BigInt::from(a / b), BigInt::from(a % b)), "{a} / {b}");
            }
        }
    }

    #[test]
    fn long_division_reconstructs_the_dividend() {
        let mut rng = Rng(0xD1B5_4A32_D192_ED03);
        for _ in 0..3_000 {
            let la = 1 + (rng.next() % 12) as usize;
            let lb = 1 + (rng.next() % 8) as usize;
            let a = rng.big(la);
            let b = rng.big(lb);
            if b.is_zero() {
                continue;
            }
            let (q, r) = a.div_rem(&b);
            assert_eq!(&(&q * &b) + &r, a, "{a} = {q}·{b} + {r}");
            assert!(r.abs() < b.abs(), "{r} vs {b}");
            assert!(r.is_zero() || r.is_negative() == a.is_negative());
        }
    }

    /// Dividends whose first quotient-digit estimate is one too large even after the
    /// two-digit test, so Algorithm D must add the divisor back (the test vectors of
    /// Warren's `divmnu64`, limbs least significant first). Random data almost never
    /// reaches that step.
    #[test]
    fn long_division_adds_back_when_the_estimate_is_one_too_large() {
        let cases: [(&[u32], &[u32], &[u32], &[u32]); 5] = [
            (&[3, 0, 0x8000_0000], &[1, 0, 0x2000_0000], &[3], &[0, 0, 0x2000_0000]),
            (&[3, 0, 0x8000], &[1, 0, 0x2000], &[3], &[0, 0, 0x2000]),
            (&[0, 0, 0x8000, 0x7fff], &[1, 0, 0x8000], &[0xfffe_0000], &[0x2_0000, 0xffff_ffff, 0x7fff]),
            (&[0, 0xfffe, 0, 0x8000], &[0xffff, 0, 0x8000], &[0xffff_ffff], &[0xffff, 0xffff_ffff, 0x7fff]),
            (&[0x7fff_ffff, 0, 0xffff_ffff], &[1, 0, 1], &[0xffff_fffe], &[0x8000_0001, 0xffff_ffff]),
        ];
        for (u, v, q, r) in cases {
            let (a, b) = (BigInt::from_parts(false, u.to_vec()), BigInt::from_parts(false, v.to_vec()));
            let (gq, gr) = a.div_rem(&b);
            assert_eq!(&(&gq * &b) + &gr, a);
            assert!(gr < b);
            assert_eq!((gq, gr), (BigInt::from_parts(false, q.to_vec()), BigInt::from_parts(false, r.to_vec())), "{a} / {b}");
        }
    }

    #[test]
    fn the_edges_of_i64_keep_one_representation() {
        let min = BigInt::from(i64::MIN);
        let max = BigInt::from(i64::MAX);
        let one = BigInt::one();
        assert_eq!(&(&max + &one) - &one, max);
        assert_eq!(&(&min - &one) + &one, min);
        assert_eq!(-&(-&min), min);
        assert_eq!((-&min).to_string(), "9223372036854775808");
        assert_eq!(min.div_rem(&BigInt::from(-1i64)).0.to_string(), "9223372036854775808");
        assert_eq!(BigInt::from(u64::MAX).to_string(), "18446744073709551615");
        assert_eq!(&BigInt::from(u64::MAX) - &BigInt::from(u64::MAX), BigInt::zero());
    }

    #[test]
    fn gcd_and_rationals_reduce_to_lowest_terms() {
        let big = &BigInt::from(i128::MAX) * &BigInt::from(6i64);
        assert_eq!(big.gcd(&BigInt::from(-4i64)), BigInt::from(2i64));
        let r = Rational::new(BigInt::from(28i64), BigInt::from(-6i64));
        assert_eq!(r.to_string(), "-14/3");
        assert_eq!(Rational::new(big.clone(), big).to_string(), "1");
        let third = Rational::new(BigInt::one(), BigInt::from(3i64));
        assert_eq!(third.add(&third).add(&third).to_string(), "1");
        assert!(third < Rational::new(BigInt::from(1i64), BigInt::from(2i64)));
        assert_eq!(third.sub(&third.mul(&Rational::from(3))).to_string(), "-2/3");
        assert_eq!(third.div(&Rational::from(-2)).to_string(), "-1/6");
    }
}
