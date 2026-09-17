//! SMT-LIB text shared by the linear queries of [VER-015], [VER-018] and [VER-019]: the
//! coefficient terms they emit and the integer definitions of the models they read.
//!
//! Every model reader goes through [`int_definition`], whose grammar is the TypeScript
//! reference's `^\(define-fun\s+(\S+)\s+\(\)\s+Int\s+(\(-\s*(\d+)\s*\)|(\d+))\s*\)$`, so
//! the implementations accept exactly the same replies.

/// `c·v`: `v` for `1`, `(- v)` for `-1`, otherwise `(* c v)` with a negative `c` written
/// `(- k)`.
pub(crate) fn term(c: i128, v: &str) -> String {
    match c {
        1 => v.to_string(),
        -1 => format!("(- {v})"),
        c if c > 0 => format!("(* {c} {v})"),
        c => format!("(* (- {}) {v})", -c),
    }
}

/// A lone term unwrapped, otherwise `(+ t1 t2 …)`; `zero` when there are none.
pub(crate) fn sum(terms: &[String], zero: &str) -> String {
    match terms {
        [] => zero.to_string(),
        [single] => single.clone(),
        _ => format!("(+ {})", terms.join(" ")),
    }
}

/// The largest magnitude the reference holds exactly (JavaScript's
/// `Number.MAX_SAFE_INTEGER`). A decoder or bound that must fail where it fails uses it.
pub(crate) const MAX_SAFE_INTEGER: i64 = (1 << 53) - 1;

/// An integer literal of a model definition, kept as its text: the readers need different
/// ranges of it, and a sign or an index is exact for any magnitude.
pub(crate) struct IntLiteral<'a> {
    negative: bool,
    digits: &'a str,
}

impl IntLiteral<'_> {
    /// The value, or `None` when it does not fit `i128`.
    pub(crate) fn value(&self) -> Option<i128> {
        let magnitude: i128 = self.digits.parse().ok()?;
        Some(if self.negative { -magnitude } else { magnitude })
    }

    /// The value, or `None` beyond ±[`MAX_SAFE_INTEGER`].
    pub(crate) fn safe_integer(&self) -> Option<i64> {
        self.value()
            .filter(|v| v.unsigned_abs() <= MAX_SAFE_INTEGER as u128)
            .map(|v| v as i64)
    }

    fn is_zero(&self) -> bool {
        self.digits.bytes().all(|b| b == b'0')
    }

    pub(crate) fn is_positive(&self) -> bool {
        !self.negative && !self.is_zero()
    }

    /// The value as an index below `count`; `None` when it is negative or not below.
    pub(crate) fn index_below(&self, count: usize) -> Option<usize> {
        if self.negative && !self.is_zero() {
            return None;
        }
        self.digits.parse::<usize>().ok().filter(|&v| v < count)
    }
}

/// Reads `(define-fun <name> () Int <lit>)`, `<lit>` a natural `k` or `(- k)`, with
/// whitespace wherever z3 may put it (it breaks the line before the literal). `None` for
/// any other shape, a `Real` definition included.
pub(crate) fn int_definition(def: &str) -> Option<(&str, IntLiteral<'_>)> {
    let rest = spaced(def.strip_prefix("(define-fun")?)?;
    let name_end = rest.find(char::is_whitespace)?;
    let (name, rest) = rest.split_at(name_end);
    let rest = spaced(rest)?.strip_prefix("()")?;
    let rest = spaced(rest)?.strip_prefix("Int")?;
    let lit = spaced(rest)?.strip_suffix(')')?.trim_end();
    let (negative, digits) = match lit.strip_prefix("(-") {
        Some(inner) => (true, inner.strip_suffix(')')?.trim()),
        None => (false, lit),
    };
    all_digits(digits).then_some((name, IntLiteral { negative, digits }))
}

/// The index of a name `<prefix><digits>`, or `None` for any other name. An index too
/// large for `usize` reads as `usize::MAX`, past every net, so a caller's range check
/// drops it where the reference's does.
pub(crate) fn indexed(name: &str, prefix: char) -> Option<usize> {
    let digits = name.strip_prefix(prefix)?;
    // Digits only: `parse` alone would take `r+3`.
    all_digits(digits).then(|| digits.parse().unwrap_or(usize::MAX))
}

fn all_digits(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())
}

/// `s` after the whitespace it must start with; `None` when it starts with none.
fn spaced(s: &str) -> Option<&str> {
    let rest = s.trim_start();
    (rest.len() < s.len()).then_some(rest)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read(def: &str) -> Option<(&str, Option<i128>)> {
        int_definition(def).map(|(name, lit)| (name, lit.value()))
    }

    #[test]
    fn reads_the_reference_grammar_and_nothing_else() {
        assert_eq!(read("(define-fun a3 () Int\n    (- 12))"), Some(("a3", Some(-12))));
        assert_eq!(read("(define-fun b () Int 0 )"), Some(("b", Some(0))));
        assert_eq!(read("(define-fun y0 () Int (-  7 ))"), Some(("y0", Some(-7))));
        for rejected in [
            "(define-fun a3 ()Int 1)",
            "(define-funa3 () Int 1)",
            "(define-fun a3 () Int1)",
            "(define-fun a3 () Int ( - 1))",
            "(define-fun a3 () Real 1.0)",
            "(define-fun a3 () Int +1)",
            "(define-fun a3 ((x Int)) Int 1)",
        ] {
            assert!(read(rejected).is_none(), "{rejected}");
        }
    }

    #[test]
    fn indexes_digits_only_and_saturates_a_huge_index() {
        assert_eq!(indexed("m07", 'm'), Some(7));
        assert_eq!(indexed("m+7", 'm'), None);
        assert_eq!(indexed("m", 'm'), None);
        assert_eq!(indexed("n7", 'm'), None);
        assert_eq!(indexed(&format!("m{}", "9".repeat(30)), 'm'), Some(usize::MAX));
    }

    fn lit(def: &str) -> IntLiteral<'_> {
        int_definition(def).expect("a definition").1
    }

    #[test]
    fn reads_a_literal_in_the_range_each_caller_needs() {
        let safe = format!("(define-fun m0 () Int (- {MAX_SAFE_INTEGER}))");
        assert_eq!(lit(&safe).safe_integer(), Some(-MAX_SAFE_INTEGER));
        let past = format!("(define-fun m0 () Int {})", MAX_SAFE_INTEGER + 1);
        assert_eq!(lit(&past).safe_integer(), None);
        assert_eq!(lit(&past).value(), Some(i128::from(MAX_SAFE_INTEGER) + 1));
        let huge = format!("(define-fun s0 () Int {})", "9".repeat(44));
        assert_eq!(lit(&huge).value(), None);
        assert!(lit(&huge).is_positive());
        assert_eq!(lit(&huge).index_below(3), None);
        assert_eq!(lit("(define-fun s0 () Int (- 0))").index_below(3), Some(0));
        assert!(!lit("(define-fun s0 () Int (- 0))").is_positive());
    }

    #[test]
    fn renders_terms_and_sums() {
        assert_eq!(term(1, "x"), "x");
        assert_eq!(term(-1, "x"), "(- x)");
        assert_eq!(term(3, "x"), "(* 3 x)");
        assert_eq!(term(-3, "x"), "(* (- 3) x)");
        assert_eq!(sum(&[], "0.0"), "0.0");
        assert_eq!(sum(&["x".to_string()], "0"), "x");
        assert_eq!(sum(&["x".to_string(), "(- y)".to_string()], "0"), "(+ x (- y))");
    }
}
