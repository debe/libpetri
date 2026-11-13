import Libpetri.Spec.Text

requirement_text MOD_060
  id "MOD-060"
  title "Fusion Set Declaration (orthogonal to composition)"
  priority MUST
  kind F
  body r#"A **fusion set** declares that N places — possibly drawn from different module instances — are to be treated as a single canonical place in the composed flat net. Fusion is **orthogonal to composition**:

1. Composition merges places via port-binding (one instance port place ↔ one caller place per binding).
2. Fusion merges N places at once via N-ary equivalence, after composition has flattened all subnet instances.

Fusion is the mechanism for modeling shared cross-instance state (e.g., a global rate limiter shared by three instances of a leaky-bucket subnet) without expressing the shared resource as an interface port on every subnet.

A fusion set has:
1. A name, used in diagnostics only. The first declared member is the canonical member, and it keeps its own name in the fused net ([MOD-061]). Whether an empty name is accepted is implementation-defined: Rust rejects it, TypeScript rejects it on the builder and accepts it in `FusionSet.of`, Java accepts it.
2. A list of N member places in the order they were declared, N >= 1. A set with one member fuses nothing: its canonical member maps to itself.
3. All members MUST have compatible token types per [CORE-003] (implementation-defined enforcement matching [MOD-022]). Java and Rust compare the run-time token types of the members; TypeScript keeps no run-time token type and checks none. The Python binding declares no fusion sets.

⟦s1|*If* a fusion set is declared with no member, *then* declaring it *shall* fail.⟧

⟦s2|*When* a fusion set is declared with a non-empty name and at least one member and no two of its members have different run-time token types, declaring it *shall* succeed and *shall* return the set with its name and with its members in the order they were declared.⟧

⟦s3|*Where* an implementation keeps a run-time token type for places (Java and Rust), *if* two members of a fusion set have different token types, *then* declaring the set *shall* fail.⟧

**Order of operations relative to composition.** Port substitution per [MOD-020] and channel merging per [MOD-021] happen **first**, during each `compose(...)` call on the enclosing builder. Fusion sets are then applied to the resulting post-composition flat net during `build()` per [MOD-061]. Consequently, fusion membership is evaluated against **post-composition place identity**: a fusion set MAY validly name a caller-side place that became the destination of one or more port substitutions. In the fused net the canonical member is the place of every arc that, after composition, was on the (now-substituted) caller place or on another member of the set, so the tokens those arcs produce and consume meet on one place. A token put on a non-canonical member when the initial marking is set is not moved: it stays on that member's name, which the fused net does not declare ([MOD-061]).

**Acceptance Criteria:**
1. A fusion set can be declared with a name and a list of N (>= 1) member places.
2. Fusion sets are independent of port bindings: the same caller place MAY be both a port-binding destination and a fusion member; applying fusion produces a flat net in which the canonical fused place is the substitution target for every arc that previously referenced any port-substituted instance place or any non-canonical fusion member.
3. Token-type incompatibility among members is rejected per [CORE-003], in the implementations that keep a run-time token type (Java and Rust).
4. Declaring a fusion set with no member is rejected as malformed; a fusion set with one member is accepted and fuses nothing.

**Depends on:** [CORE-003], [MOD-020]
**Test derivation:** Declare a fusion set with three members of type `Token<Permit>`; verify accepted. Declare with one member; verify it is accepted and the built net is unchanged. Declare with no member; verify rejection. Declare with mixed token types (Java and Rust); verify rejection. Compose an instance binding port `out -> P`, then declare a fusion set `{P, Q}`; build; verify the canonical fused place is the substitution target of every arc that previously referenced the renamed instance port place or `Q`."#
