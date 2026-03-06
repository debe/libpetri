/// Number of bits per word.
pub const WORD_BITS: usize = 64;
/// Shift amount to convert bit index to word index.
pub const WORD_SHIFT: usize = 6;
/// Mask to extract bit position within a word.
pub const WORD_MASK: usize = 63;

/// Returns the number of u64 words needed to represent `n` bits.
#[inline]
pub fn word_count(n: usize) -> usize {
    (n + WORD_BITS - 1) >> WORD_SHIFT
}

/// Sets bit `i` in the bitmap.
#[inline]
pub fn set_bit(words: &mut [u64], i: usize) {
    words[i >> WORD_SHIFT] |= 1u64 << (i & WORD_MASK);
}

/// Clears bit `i` in the bitmap.
#[inline]
pub fn clear_bit(words: &mut [u64], i: usize) {
    words[i >> WORD_SHIFT] &= !(1u64 << (i & WORD_MASK));
}

/// Tests if bit `i` is set.
#[inline]
pub fn test_bit(words: &[u64], i: usize) -> bool {
    (words[i >> WORD_SHIFT] & (1u64 << (i & WORD_MASK))) != 0
}

/// Returns true if all bits set in `mask` are also set in `snapshot`.
/// Equivalent to: (snapshot & mask) == mask
#[inline]
pub fn contains_all(snapshot: &[u64], mask: &[u64]) -> bool {
    debug_assert_eq!(snapshot.len(), mask.len());
    match mask.len() {
        0 => true,
        1 => (snapshot[0] & mask[0]) == mask[0],
        _ => scalar_contains_all(snapshot, mask),
    }
}

#[inline]
fn scalar_contains_all(snapshot: &[u64], mask: &[u64]) -> bool {
    for i in 0..mask.len() {
        if (snapshot[i] & mask[i]) != mask[i] {
            return false;
        }
    }
    true
}

/// Returns true if any bit set in `mask` is also set in `snapshot`.
/// Equivalent to: (snapshot & mask) != 0
#[inline]
pub fn intersects(snapshot: &[u64], mask: &[u64]) -> bool {
    debug_assert_eq!(snapshot.len(), mask.len());
    match mask.len() {
        0 => false,
        1 => (snapshot[0] & mask[0]) != 0,
        _ => scalar_intersects(snapshot, mask),
    }
}

#[inline]
fn scalar_intersects(snapshot: &[u64], mask: &[u64]) -> bool {
    for i in 0..mask.len() {
        if (snapshot[i] & mask[i]) != 0 {
            return true;
        }
    }
    false
}

/// Iterates over all set bits in the bitmap, calling `f` for each bit index.
/// Uses Kernighan's trick with trailing zero count for efficient iteration.
#[inline]
pub fn for_each_set_bit(words: &[u64], mut f: impl FnMut(usize)) {
    for (word_idx, &word) in words.iter().enumerate() {
        let base = word_idx << WORD_SHIFT;
        let mut w = word;
        while w != 0 {
            let tz = w.trailing_zeros() as usize;
            f(base + tz);
            w &= w - 1; // clear lowest set bit
        }
    }
}

/// Copies `src` bitmap OR'd into `dst`.
#[inline]
pub fn or_into(dst: &mut [u64], src: &[u64]) {
    debug_assert_eq!(dst.len(), src.len());
    for i in 0..dst.len() {
        dst[i] |= src[i];
    }
}

/// Returns true if all bits are zero.
#[inline]
pub fn is_empty(words: &[u64]) -> bool {
    words.iter().all(|&w| w == 0)
}

/// Clears all bits.
#[inline]
pub fn clear_all(words: &mut [u64]) {
    for w in words.iter_mut() {
        *w = 0;
    }
}

/// Swaps contents of two bitmaps of the same length.
#[inline]
pub fn swap(a: &mut [u64], b: &mut [u64]) {
    debug_assert_eq!(a.len(), b.len());
    for i in 0..a.len() {
        std::mem::swap(&mut a[i], &mut b[i]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn word_count_values() {
        assert_eq!(word_count(0), 0);
        assert_eq!(word_count(1), 1);
        assert_eq!(word_count(64), 1);
        assert_eq!(word_count(65), 2);
        assert_eq!(word_count(128), 2);
        assert_eq!(word_count(129), 3);
    }

    #[test]
    fn set_clear_test_bit() {
        let mut bm = vec![0u64; 2];
        set_bit(&mut bm, 0);
        assert!(test_bit(&bm, 0));
        assert!(!test_bit(&bm, 1));

        set_bit(&mut bm, 65);
        assert!(test_bit(&bm, 65));

        clear_bit(&mut bm, 0);
        assert!(!test_bit(&bm, 0));
        assert!(test_bit(&bm, 65));
    }

    #[test]
    fn contains_all_works() {
        let snapshot = vec![0b1111u64];
        let mask = vec![0b0101u64];
        assert!(contains_all(&snapshot, &mask));

        let mask2 = vec![0b10000u64];
        assert!(!contains_all(&snapshot, &mask2));
    }

    #[test]
    fn contains_all_empty() {
        let empty: Vec<u64> = vec![];
        assert!(contains_all(&empty, &empty));
    }

    #[test]
    fn intersects_works() {
        let snapshot = vec![0b1010u64];
        let mask = vec![0b0010u64];
        assert!(intersects(&snapshot, &mask));

        let mask2 = vec![0b0101u64];
        assert!(!intersects(&snapshot, &mask2));
    }

    #[test]
    fn for_each_set_bit_works() {
        let bm = vec![0b1010_0101u64, 0u64];
        let mut bits = Vec::new();
        for_each_set_bit(&bm, |i| bits.push(i));
        assert_eq!(bits, vec![0, 2, 5, 7]);
    }

    #[test]
    fn for_each_set_bit_multi_word() {
        let mut bm = vec![0u64; 2];
        set_bit(&mut bm, 0);
        set_bit(&mut bm, 63);
        set_bit(&mut bm, 64);
        set_bit(&mut bm, 127);
        let mut bits = Vec::new();
        for_each_set_bit(&bm, |i| bits.push(i));
        assert_eq!(bits, vec![0, 63, 64, 127]);
    }

    #[test]
    fn or_into_works() {
        let mut dst = vec![0b1010u64];
        let src = vec![0b0101u64];
        or_into(&mut dst, &src);
        assert_eq!(dst[0], 0b1111);
    }

    #[test]
    fn is_empty_works() {
        assert!(is_empty(&[0u64, 0u64]));
        assert!(!is_empty(&[0u64, 1u64]));
    }
}
