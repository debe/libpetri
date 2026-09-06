use std::collections::HashSet;
use std::sync::Arc;

use libpetri_core::output::Out;
// Only the async (`tokio`) timeout path consumes these; gate the imports so
// feature-free builds don't flag them as unused.
#[cfg(feature = "tokio")]
use std::collections::HashMap;
#[cfg(feature = "tokio")]
use libpetri_core::context::OutputEntry;
#[cfg(feature = "tokio")]
use libpetri_core::token::{ErasedToken, Token};

/// \[IO-015\] output validation as an **exact-explanation search**.
///
/// An *assignment* selects exactly one child at each [`Out::Xor`] it
/// reaches; subtrees under an unselected child are never evaluated. Each
/// assignment *claims* a set of places:
///
/// - [`Out::Place`] / [`Out::ForwardInput`] — claims the named place.
/// - [`Out::And`] — claims the union of every child's claim. The children
///   are an **unordered** set of obligations, so the verdict cannot depend
///   on the order they were declared in (\[IO-015\] AC8).
/// - [`Out::Xor`] — claims the selected child's claim.
/// - [`Out::Timeout`] — claims its child's claim.
///
/// Validation succeeds iff **exactly one** assignment's claim *equals* the
/// produced set. Zero is a violation (nothing explains the write), two or
/// more is a violation (the write is genuinely ambiguous).
///
/// Equality — rather than "every obligation was satisfied" — is what makes
/// a token written to a declared place *outside* the selected branch a
/// violation instead of a silent deposit (AC9), and it removes the need for
/// the old subsumption tie-break: `xor(and(a, b, c), and(a, b))` with a, b
/// and c produced has exactly one *exact* claim (AC5).
///
/// Returns a plain `bool` so the firing hot path stays branch-and-return;
/// [`describe_out_violation`] renders the reason on the (cold) failure path.
/// `scratch` is the caller's pooled claim buffer, so a satisfied firing
/// allocates nothing.
pub(crate) fn validate_out_spec(
    out: &Out,
    produced_places: &HashSet<Arc<str>>,
    scratch: &mut Vec<u64>,
) -> bool {
    matches!(verdict(out, produced_places, scratch), Verdict::Conforms)
}

/// Explains why `produced_places` failed [`validate_out_spec`]. Cold
/// path — only called to populate a `TransitionFailed` event, so it may
/// re-walk the spec and allocate freely. The wording matches Java and
/// TypeScript so the three runtimes stay diagnosable the same way.
#[cold]
#[inline(never)]
pub(crate) fn describe_out_violation(out: &Out, produced_places: &HashSet<Arc<str>>) -> String {
    let index = ProducedIndex::build(out, produced_places);
    let wrote = index.names.join(", ");
    if search_with(out, &index) == Verdict::Ambiguous {
        format!(
            "ambiguous output - {{{wrote}}} is claimed by more than one branch of {}",
            describe(out)
        )
    } else {
        format!(
            "output does not match the declared spec - produced {{{wrote}}}, \
             which no single branch of {} claims exactly",
            describe(out)
        )
    }
}

/// Renders the declared spec for a violation message. The leading phrase of the
/// message matches Java and TypeScript so the three stay diagnosable the same
/// way; this suffix is extra detail Rust has always carried, and dropping it to
/// match the others exactly would have been a regression for no gain.
fn describe(out: &Out) -> String {
    match out {
        Out::Place(p) => format!("'{}'", p.name()),
        Out::ForwardInput { from, to } => format!("forward('{}' -> '{}')", from.name(), to.name()),
        Out::And(children) => format!("and({})", describe_all(children)),
        Out::Xor(children) => format!("xor({})", describe_all(children)),
        Out::Timeout { after_ms, child } => {
            format!("timeout({}ms, {})", after_ms, describe(child))
        }
    }
}

fn describe_all(children: &[Out]) -> String {
    children.iter().map(describe).collect::<Vec<_>>().join(", ")
}

/// Outcome of the exact-explanation search.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    /// Exactly one assignment claims exactly the produced set.
    Conforms,
    /// No assignment claims exactly the produced set.
    Unexplained,
    /// Two or more assignments do.
    Ambiguous,
}

fn verdict(out: &Out, produced: &HashSet<Arc<str>>, scratch: &mut Vec<u64>) -> Verdict {
    let index = ProducedIndex::build(out, produced);
    if index.width() <= 64 {
        search(out, &index, scratch)
    } else {
        search::<WideMask>(out, &index, &mut Vec::new())
    }
}

/// [`verdict`] without a caller-supplied buffer. Cold path only.
fn search_with(out: &Out, index: &ProducedIndex<'_>) -> Verdict {
    if index.width() <= 64 {
        search::<u64>(out, index, &mut Vec::new())
    } else {
        search::<WideMask>(out, index, &mut Vec::new())
    }
}

// ==================== The search ====================

/// Bit index over the produced places the spec actually names, sorted.
///
/// Restricting equality to places the spec *names* is load-bearing: a token
/// produced to a place the spec never mentions is \[CORE-072\]'s business —
/// retained in the marking and reported as an unknown place — not an
/// \[IO-015\] violation. Indexing the raw produced set instead would make
/// every claim unmatchable as soon as one such token existed.
///
/// Duplicate names collapse to one bit, so `xor(place(a), place(a))` is seen
/// as two assignments claiming the *same* set (ambiguous, AC4) rather than
/// two assignments claiming half of a two-bit universe each.
struct ProducedIndex<'a> {
    /// `produced ∩ names(spec)`, sorted and deduped. Sorted so the bit
    /// lookup is a binary search and the diagnostic's place list is stable.
    names: Vec<&'a str>,
}

impl<'a> ProducedIndex<'a> {
    fn build(out: &'a Out, produced: &HashSet<Arc<str>>) -> Self {
        let mut names = Vec::new();
        collect_index(out, produced, &mut names);
        names.sort_unstable();
        names.dedup();
        Self { names }
    }

    fn width(&self) -> usize {
        self.names.len()
    }

    fn bit(&self, name: &str) -> Option<usize> {
        self.names.binary_search(&name).ok()
    }
}

fn collect_index<'a>(out: &'a Out, produced: &HashSet<Arc<str>>, names: &mut Vec<&'a str>) {
    match out {
        Out::Place(p) => {
            if produced.contains(p.name()) {
                names.push(p.name());
            }
        }
        Out::ForwardInput { to, .. } => {
            if produced.contains(to.name()) {
                names.push(to.name());
            }
        }
        Out::And(children) | Out::Xor(children) => {
            for child in children {
                collect_index(child, produced, names);
            }
        }
        Out::Timeout { child, .. } => collect_index(child, produced, names),
    }
}

/// A claimed set of places, as a bitset over [`ProducedIndex`].
///
/// `u64` covers every spec whose produced-and-named set fits in 64 places,
/// which it always does in practice, and keeps the search allocation-free.
/// [`WideMask`] is the correctness fallback past that.
trait Mask: Clone + PartialEq {
    fn empty(width: usize) -> Self;
    fn single(width: usize, bit: usize) -> Self;
    fn union_with(&mut self, other: &Self);
    fn count(&self) -> usize;
}

impl Mask for u64 {
    fn empty(_width: usize) -> Self {
        0
    }
    fn single(_width: usize, bit: usize) -> Self {
        1u64 << bit
    }
    fn union_with(&mut self, other: &Self) {
        *self |= *other;
    }
    fn count(&self) -> usize {
        self.count_ones() as usize
    }
}

/// Multi-word fallback for the (unreached in practice) case of a spec that
/// names more than 64 of the produced places.
type WideMask = Vec<u64>;

impl Mask for WideMask {
    fn empty(width: usize) -> Self {
        vec![0u64; width.div_ceil(64)]
    }
    fn single(width: usize, bit: usize) -> Self {
        let mut words = vec![0u64; width.div_ceil(64)];
        words[bit / 64] = 1u64 << (bit % 64);
        words
    }
    fn union_with(&mut self, other: &Self) {
        for (a, b) in self.iter_mut().zip(other.iter()) {
            *a |= *b;
        }
    }
    fn count(&self) -> usize {
        self.iter().map(|w| w.count_ones() as usize).sum()
    }
}

fn search<M: Mask>(out: &Out, index: &ProducedIndex<'_>, buf: &mut Vec<M>) -> Verdict {
    buf.clear();
    collect_claims(out, index, buf);
    let width = index.width();
    let mut exact = 0usize;
    for claim in buf.iter() {
        // Every claim is a subset of the indexed set by construction — a leaf
        // only claims a place that was produced — so an equal popcount means
        // an equal set.
        if claim.count() == width {
            exact += 1;
            if exact > 1 {
                break;
            }
        }
    }
    match exact {
        0 => Verdict::Unexplained,
        1 => Verdict::Conforms,
        _ => Verdict::Ambiguous,
    }
}

/// Appends the claim of every assignment whose claim is a subset of the
/// produced set to `buf`.
///
/// The subset restriction is the pruning that keeps this linear in practice:
/// a leaf naming a place that was not produced contributes nothing, so a
/// `xor` branch dies as soon as it claims something unwritten and an `and`
/// dies with any unsatisfiable child. Branching survives only where several
/// `xor` children are simultaneously consistent with what was produced —
/// the ambiguous case, which is rejected anyway.
fn collect_claims<M: Mask>(out: &Out, index: &ProducedIndex<'_>, buf: &mut Vec<M>) {
    match out {
        Out::Place(p) => push_leaf(p.name(), index, buf),
        Out::ForwardInput { to, .. } => push_leaf(to.name(), index, buf),
        Out::Timeout { child, .. } => collect_claims(child, index, buf),

        Out::Xor(children) => {
            let start = buf.len();
            for child in children {
                collect_claims(child, index, buf);
            }
            cap_multiplicity(buf, start);
        }

        Out::And(children) => {
            // Unordered: a join over the children's claim sets, so the result
            // cannot depend on their declaration order ([IO-015] AC8).
            let start = buf.len();
            buf.push(M::empty(index.width()));
            for child in children {
                let acc_end = buf.len();
                collect_claims(child, index, buf);
                if buf.len() == acc_end {
                    // No assignment satisfies this child, so none satisfies
                    // the `and`.
                    buf.truncate(start);
                    return;
                }
                // Cross the accumulator in [start, acc_end) with the child's
                // claims in [acc_end, child_end), appending the products past
                // child_end, then drop both operands.
                let child_end = buf.len();
                for i in start..acc_end {
                    for j in acc_end..child_end {
                        let mut merged = buf[i].clone();
                        merged.union_with(&buf[j]);
                        buf.push(merged);
                    }
                }
                buf.drain(start..child_end);
                cap_multiplicity(buf, start);
            }
        }
    }
}

fn push_leaf<M: Mask>(name: &str, index: &ProducedIndex<'_>, buf: &mut Vec<M>) {
    if let Some(bit) = index.bit(name) {
        buf.push(M::single(index.width(), bit));
    }
}

/// Collapses identical claims in `buf[start..]`, keeping at most two of each.
///
/// Load-bearing, not an optimisation. Validation only needs to distinguish
/// "no assignment", "exactly one" and "more than one", so a third assignment
/// claiming an already-seen set carries no information. Without the cap the
/// `and` join is O(2^k) in the number of `xor` children on a path that runs
/// on *every* firing — TypeScript measured 21us at k=8 and seconds at k=20.
/// With it the working set is bounded by twice the number of *distinct*
/// claim subsets, which is what the produced set can actually distinguish.
fn cap_multiplicity<M: Mask>(buf: &mut Vec<M>, start: usize) {
    if buf.len() - start < 3 {
        return;
    }
    let mut write = start;
    let mut read = start;
    while read < buf.len() {
        let mut kept = 0usize;
        for k in start..write {
            if buf[k] == buf[read] {
                kept += 1;
            }
        }
        if kept < 2 {
            buf.swap(write, read);
            write += 1;
        }
        read += 1;
    }
    buf.truncate(write);
}

/// Build the list of outputs to produce when an [`Out::Timeout`]
/// branch fires (the async action exceeded its `after_ms` budget).
/// Each leaf [`Out::Place`] under the timeout `child` becomes one
/// unit-valued token at that place name; [`Out::And`] flattens
/// recursively; [`Out::ForwardInput`] re-emits the consumed input
/// token(s) at the forward target, satisfying \[EXEC-022\] criterion 3.
///
/// `forwarded` maps each `from` place name to the token(s) consumed
/// from it, snapshotted *before* the action was spawned — the action's
/// [`TransitionContext`](libpetri_core::context::TransitionContext),
/// which owns the consumed tokens, is dropped when the action future is
/// cancelled on timeout, so the values must be captured up front.
///
/// **Unsupported under a `Timeout`** (programmer errors — the builder
/// should reject them, so we panic):
/// - [`Out::Xor`] — ambiguous which branch to fire on timeout.
/// - Nested [`Out::Timeout`] — meaningless; one budget per action.
///
/// Only reachable from the async (`tokio`) path; gated so feature-free
/// builds don't flag it as dead code.
#[cfg(feature = "tokio")]
pub(crate) fn timeout_outputs(
    child: &Out,
    forwarded: &HashMap<Arc<str>, Vec<ErasedToken>>,
) -> Vec<OutputEntry> {
    let mut out = Vec::new();
    collect_timeout_outputs(child, forwarded, &mut out);
    out
}

#[cfg(feature = "tokio")]
fn collect_timeout_outputs(
    out: &Out,
    forwarded: &HashMap<Arc<str>, Vec<ErasedToken>>,
    result: &mut Vec<OutputEntry>,
) {
    match out {
        Out::Place(p) => {
            let token = ErasedToken::from_typed(&Token::new(()));
            result.push(OutputEntry {
                place_name: Arc::clone(p.name_arc()),
                token,
            });
        }
        Out::And(children) => {
            for c in children {
                collect_timeout_outputs(c, forwarded, result);
            }
        }
        Out::Xor(_) => {
            // Spec parity with Java: panicking here is a programmer
            // error — the net builder accepted an Xor under a Timeout
            // which is not a meaningful semantic.
            panic!("Out::Xor is not allowed inside Out::Timeout child");
        }
        Out::Timeout { .. } => {
            panic!("Nested Out::Timeout is not allowed");
        }
        Out::ForwardInput { from, to } => {
            // [EXEC-022] criterion 3: forward the consumed input
            // token(s) from `from` to `to`. The values were snapshotted
            // before the action spawned (see `timeout_outputs`).
            if let Some(tokens) = forwarded.get(from.name()) {
                for token in tokens {
                    result.push(OutputEntry {
                        place_name: Arc::clone(to.name_arc()),
                        token: token.clone(),
                    });
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::output::{and, forward_input, out_place, timeout, xor};
    use libpetri_core::place::Place;

    fn produced(names: &[&str]) -> HashSet<Arc<str>> {
        names.iter().map(|n| Arc::<str>::from(*n)).collect()
    }

    fn v(out: &Out, names: &[&str]) -> Verdict {
        let set = produced(names);
        let got = verdict(out, &set, &mut Vec::new());
        // `validate_out_spec` is the same search, so the two must agree.
        assert_eq!(
            validate_out_spec(out, &set, &mut Vec::new()),
            got == Verdict::Conforms
        );
        got
    }

    fn message(out: &Out, names: &[&str]) -> String {
        describe_out_violation(out, &produced(names))
    }

    fn p(name: &str) -> Place<i32> {
        Place::<i32>::new(name)
    }

    #[test]
    fn place_spec_satisfied() {
        assert_eq!(v(&out_place(&p("a")), &["a"]), Verdict::Conforms);
    }

    #[test]
    fn place_spec_not_satisfied() {
        assert_eq!(v(&out_place(&p("a")), &[]), Verdict::Unexplained);
        assert!(message(&out_place(&p("a")), &[]).starts_with("output does not match the declared spec"));
    }

    #[test]
    fn and_all_satisfied() {
        let spec = and(vec![out_place(&p("a")), out_place(&p("b"))]);
        assert_eq!(v(&spec, &["a", "b"]), Verdict::Conforms);
    }

    #[test]
    fn and_partially_satisfied_is_a_violation() {
        let spec = and(vec![out_place(&p("a")), out_place(&p("b"))]);
        assert_eq!(v(&spec, &["a"]), Verdict::Unexplained);
    }

    #[test]
    fn xor_exactly_one_branch() {
        let spec = xor(vec![out_place(&p("a")), out_place(&p("b"))]);
        assert_eq!(v(&spec, &["b"]), Verdict::Conforms);
    }

    #[test]
    fn xor_no_branch_is_a_violation() {
        let spec = xor(vec![out_place(&p("a")), out_place(&p("b"))]);
        assert_eq!(v(&spec, &[]), Verdict::Unexplained);
    }

    /// Both branches written: neither branch *claims* `{a, b}` — one claims
    /// `{a}`, the other `{b}` — so under the equality rule this is unexplained
    /// output rather than two competing matches.
    #[test]
    fn xor_both_branches_written_is_a_violation() {
        let spec = xor(vec![out_place(&p("a")), out_place(&p("b"))]);
        assert_eq!(v(&spec, &["a", "b"]), Verdict::Unexplained);
        assert_eq!(
            message(&spec, &["a", "b"]),
            "output does not match the declared spec - produced {a, b}, \
             which no single branch of xor('a', 'b') claims exactly"
        );
    }

    #[test]
    fn xor_with_nested_and_selects_the_written_branch() {
        let spec = xor(vec![
            and(vec![out_place(&p("a")), out_place(&p("b"))]),
            and(vec![out_place(&p("c")), out_place(&p("d"))]),
        ]);
        assert_eq!(v(&spec, &["c", "d"]), Verdict::Conforms);
    }

    /// \[IO-015\] AC5: `xor(and(a,b,c), and(a,b))` with a, b, c produced has
    /// exactly one *exact* claim, so it resolves with no subsumption
    /// tie-break — the rule the spec used to need and no longer has.
    #[test]
    fn overlapping_branches_resolve_without_a_tie_break() {
        let spec = xor(vec![
            and(vec![out_place(&p("a")), out_place(&p("b")), out_place(&p("c"))]),
            and(vec![out_place(&p("a")), out_place(&p("b"))]),
        ]);
        assert_eq!(v(&spec, &["a", "b", "c"]), Verdict::Conforms);
    }

    /// Neither `and(a,b)` nor `and(b,c)` claims all of `{a, b, c}`, so nothing
    /// explains the write.
    #[test]
    fn genuinely_overlapping_branches_are_a_violation() {
        let spec = xor(vec![
            and(vec![out_place(&p("a")), out_place(&p("b"))]),
            and(vec![out_place(&p("b")), out_place(&p("c"))]),
        ]);
        assert_eq!(v(&spec, &["a", "b", "c"]), Verdict::Unexplained);
    }

    /// \[IO-015\] AC8: `and` is unordered. The old eager walk short-circuited
    /// on its first unsatisfied child while an inner `xor` with no satisfied
    /// child failed outright, so `and(a, xor(c, d))` and `and(xor(c, d), a)`
    /// could disagree on the same write set.
    #[test]
    fn and_is_unordered() {
        let forward = and(vec![
            out_place(&p("a")),
            xor(vec![out_place(&p("c")), out_place(&p("d"))]),
        ]);
        let reversed = and(vec![
            xor(vec![out_place(&p("c")), out_place(&p("d"))]),
            out_place(&p("a")),
        ]);
        for names in [&[][..], &["a"][..], &["c"][..], &["a", "c"][..], &["a", "c", "d"][..]] {
            assert_eq!(
                v(&forward, names),
                v(&reversed, names),
                "child order changed the verdict for produced={names:?}"
            );
        }
        assert_eq!(v(&forward, &["a", "c"]), Verdict::Conforms);
        assert_eq!(v(&forward, &["a"]), Verdict::Unexplained);
    }

    /// \[IO-015\] AC9: selecting `b` explains b but leaves c unexplained. c
    /// used to be deposited silently because validation only checked that the
    /// selected branch's obligations were met.
    #[test]
    fn write_outside_the_selected_branch_is_a_violation() {
        let spec = xor(vec![
            and(vec![out_place(&p("a")), out_place(&p("c"))]),
            out_place(&p("b")),
        ]);
        assert_eq!(v(&spec, &["b", "c"]), Verdict::Unexplained);
    }

    /// \[IO-015\] AC10: the second branch claims exactly `{a}`. The old eager
    /// walk failed inside the first branch's inner `xor` before the enclosing
    /// one could try its sibling.
    #[test]
    fn inner_xor_does_not_preempt_the_outer_one() {
        let spec = xor(vec![
            and(vec![
                out_place(&p("a")),
                xor(vec![out_place(&p("c")), out_place(&p("d"))]),
            ]),
            out_place(&p("a")),
        ]);
        assert_eq!(v(&spec, &["a"]), Verdict::Conforms);
    }

    /// \[IO-015\] AC4: two branches whose claims are both exactly `{a}` are
    /// genuinely ambiguous.
    #[test]
    fn two_branches_claiming_the_same_set_are_ambiguous() {
        let spec = xor(vec![and(vec![out_place(&p("a"))]), out_place(&p("a"))]);
        assert_eq!(v(&spec, &["a"]), Verdict::Ambiguous);
        assert_eq!(
            message(&spec, &["a"]),
            "ambiguous output - {a} is claimed by more than one branch of xor(and('a'), 'a')"
        );
    }

    /// A token in a place the spec never names is \[CORE-072\]'s business —
    /// retained and warned about — not an \[IO-015\] violation. Comparing
    /// claims against the raw produced set would make every claim unmatchable.
    #[test]
    fn token_in_an_unnamed_place_is_not_an_io_015_violation() {
        assert_eq!(
            v(&out_place(&p("a")), &["a", "undeclared"]),
            Verdict::Conforms
        );
        let spec = and(vec![out_place(&p("a")), out_place(&p("b"))]);
        assert_eq!(v(&spec, &["a", "b", "ghost"]), Verdict::Conforms);
    }

    #[test]
    fn timeout_delegates_to_its_child() {
        let spec = timeout(100, out_place(&p("timeout")));
        assert_eq!(v(&spec, &["timeout"]), Verdict::Conforms);
        assert_eq!(v(&spec, &[]), Verdict::Unexplained);
    }

    #[test]
    fn forward_input_claims_its_target() {
        let spec = forward_input(&p("from"), &p("to"));
        assert_eq!(v(&spec, &["to"]), Verdict::Conforms);
        assert_eq!(v(&spec, &["from"]), Verdict::Unexplained);
    }

    /// The `u64` bitmask covers a spec naming up to 64 produced places; past
    /// that the search falls back to a multi-word mask and must stay exact.
    #[test]
    fn more_than_64_produced_places_still_validates_exactly() {
        let places: Vec<Place<i32>> = (0..70).map(|i| Place::<i32>::new(format!("p{i:02}"))).collect();
        let spec = and(places.iter().map(out_place).collect());
        let all: Vec<String> = (0..70).map(|i| format!("p{i:02}")).collect();
        let all_refs: Vec<&str> = all.iter().map(String::as_str).collect();
        assert_eq!(v(&spec, &all_refs), Verdict::Conforms);
        assert_eq!(v(&spec, &all_refs[..69]), Verdict::Unexplained);
    }

    /// The multiplicity cap keeps the `and` join from going exponential when
    /// every `xor` child is consistent with what was produced. Without it this
    /// enumerates 2^20 claims; the verdict must be unchanged either way.
    #[test]
    fn identical_claims_collapse_instead_of_exploding() {
        let a = p("a");
        let spec = and(
            (0..20)
                .map(|_| xor(vec![out_place(&a), out_place(&a)]))
                .collect(),
        );
        // Every assignment claims {a}, and there is more than one of them.
        assert_eq!(v(&spec, &["a"]), Verdict::Ambiguous);
    }
}
