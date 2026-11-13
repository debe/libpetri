import Libpetri.Spec.Text

requirement_text MOD_061
  id "MOD-061"
  title "Fusion Resolution at build()"
  priority MUST
  kind F
  body r#"When `build()` is invoked on an enclosing builder containing one or more fusion sets, the builder MUST:

1. For each fusion set, take its first declared member as the canonical member; the canonical member keeps its own name, and the name of the fusion set is used in diagnostics only.
2. Run a structural rewrite over every transition in the builder, substituting every non-canonical member with the canonical member in every input, output, inhibitor, read, and reset arc. When at least one input arc of a transition is on a member that is not the first declared member of its fusion set, all input arcs of that transition are reconciled after substitution by the canonical merge table of [MOD-021], with the same rejection cases and the same diagnostic shape; the seam is `Fusion set '<name>'`, where `<name>` is the name of the fusion set that lists the place of the pair, or the name of that place when no fusion set lists it. A transition with no such input arc is not merged, so duplicate input arcs it already had stay and the transition builder rejects them ([CORE-030]). Read, inhibitor and reset arcs that land on one place are kept as they are. Every rewritten transition passes through the transition builder again: the checks of [CORE-030], [IO-011], [IO-012] and [EXEC-012] apply to it, and a rewrite they reject fails `build()`.
3. Remove non-canonical members from the builder's place set; the canonical member remains. A terminal place ([EXEC-042]) declared on a non-canonical member names the canonical member in the built net.
4. Produce the resulting flat `PetriNet`.

Fusion MUST be applied **after** all `compose(...)` calls have flattened subnet instances into the builder. Fusion membership is checked against the **post-composition** place identity per [MOD-060]: a member may be any place that exists in the builder after all compositions, including caller places that became port-substitution destinations during `compose(...)`. The fusion rewrite MUST be applied before [CORE-040] returns the immutable net so that no downstream consumer sees the un-fused intermediate state. Removed members lose their subnet membership entry ([MOD-026]), and the retired-port check of [MOD-027] runs on the fused net.

**Ordering of multiple fusion sets: commutative when disjoint.** When the enclosing builder declares two or more fusion sets, `build()` applies them in an implementation-defined order. If the member sets of every pair of declared fusion sets are pairwise **disjoint** (no place is a member of more than one fusion set), the final flat net MUST be independent of that order: the result is observationally identical regardless of which fusion set is rewritten first. The order of application is internal to `build()`, so this is stated as independence from the order in which the fusion sets are declared; the order in which the built net lists its places is not part of it. Declaring two fusion sets that differ in name or in members and share a place MUST be rejected at build with a message naming a shared place and two fusion sets that list it, since the canonical choice and the order of application would otherwise alter the final structure. Declaring the same fusion set (same name, same members) twice is implementation-defined.

The result is a flat `PetriNet` per [MOD-023]; downstream consumers (executor, exporter, verifier, debug protocol) require no awareness of fusion.

The built net keeps no record of the fusion sets. An initial marking for a fused net names the canonical member: a token put on a non-canonical member stays on that name, which the built net does not declare, and is retained and inert per [CORE-072].

⟦s1|*When* fusion at `build()` succeeds on fusion sets of which no two share a member, the transitions of the result *shall* be the builder's transitions, in the same order and number, each with every member of a fusion set replaced by the first declared member of that set in every input, inhibitor, read and reset arc and in the output specification, with its name, timing, priority and action unchanged and, where at least one of its declared input arcs is on a member that is not the first declared member of its set, with its input arcs merged by the canonical merge table of [MOD-021] into one arc per place at the position of the first arc on that place.⟧

⟦s2|*When* fusion at `build()` succeeds, every transition of the result *shall* pass the checks of the transition builder ([CORE-030], [IO-011], [IO-012], [EXEC-012]).⟧

⟦s3|*When* fusion at `build()` succeeds on fusion sets of which no two share a member, the set of places of the result *shall* be the builder's places other than the members that are not the first declared member of their fusion set, together with the places a transition of the result names and the terminal places of the result.⟧

⟦s4|*When* fusion at `build()` succeeds on fusion sets of which no two share a member, the set of terminal places ([EXEC-042]) of the result *shall* be the declared terminal places with every member of a fusion set replaced by the first declared member of that set.⟧

⟦s5|*Where* no two declared fusion sets share a member, the outcome of fusion at `build()` *shall* be the same for every order in which the fusion sets are declared: the same failure with the same message, or a fused net with the same transitions in the same order, the same set of places and the same set of terminal places.⟧

⟦s6|*When* no two declared fusion sets share a member and the rewrite of every transition meets no pair of input arcs that the canonical merge table of [MOD-021] does not list and passes the checks of the transition builder, fusion at `build()` *shall* succeed.⟧

⟦s7|*If* no two declared fusion sets share a member and merging the input arcs of a rewritten transition meets two arcs on one place whose pair the canonical merge table of [MOD-021] does not list, *then* fusion at `build()` *shall* fail.⟧

⟦s8|*If* no two declared fusion sets share a member and the transition builder rejects the rewrite of a transition, *then* fusion at `build()` *shall* fail.⟧

⟦s9|*If* two declared fusion sets that differ in name or in members share a member, *then* fusion at `build()` *shall* fail with the message `Fusion overlap: place '<p>' appears in two fusion sets ('<first>' and '<second>'). A place may appear in at most one fusion set (MOD-060).`, where `<p>` is a member that two declared fusion sets both list and `<first>` and `<second>` are the names of those two sets, the one declared first named first.⟧

⟦s10|*If* exactly two fusion sets that differ in name or in members are declared and they share exactly one member `p`, *then* the message of that failure *shall* name `p`, then the set declared first, then the set declared second.⟧

⟦s11|*If* every transition before a transition `t` rewrites and passes the checks of the transition builder, no two declared fusion sets share a member, and the first off-table pair met while merging the input arcs of `t` lies on a member of a fusion set, *then* fusion at `build()` *shall* fail with the [MOD-021] rule (c) diagnostic for that pair, whose earlier side is the merge of the arcs before it on that place, whose seam is `Fusion set '<name>'` with the name of that set, and whose method spelling is one of the two that [MOD-021] allows.⟧

⟦s12|*If* every transition before a transition `t` rewrites and passes the checks of the transition builder, no two declared fusion sets share a member, and the first off-table pair met while merging the input arcs of `t` lies on a place that no fusion set lists, *then* fusion at `build()` *shall* fail with the same diagnostic, the name of that place standing in the seam for the name of a set.⟧

**Acceptance Criteria:**
1. Three instances of a leaky-bucket subnet share a global rate-limiter via a single fusion set over their three internal limiter places. The built net contains one canonical limiter place; arcs that originally referenced any of the three members now reference the canonical.
2. Tokens put on a non-canonical member at initial-marking time stay on that undeclared name, retained and inert per [CORE-072]; tokens meant for the fused place are put on the canonical member.
3. Non-canonical member places do NOT appear in the built net's place set.
4. Fusion is applied after composition: composing then fusing is observationally equivalent to writing a single hand-written net with the fused topology directly. Input arcs colliding on the canonical place follow the [MOD-021] merge table; off-table pairings are rejected at build with the diagnostic naming the fusion set.
5. Re-exporting and re-verifying the fused net works without any awareness of fusion in the consumer.
6. Multiple fusion sets with **disjoint** member sets are commutative: building the same enclosing builder twice, with its fusion sets declared in opposite orders, MUST produce flat nets that are observationally identical (identical place set, transition set, arc topology, executor behavior), or the same rejection with the same message.
7. Declaring two fusion sets that differ in name or in members and share at least one place MUST be rejected at build with a message naming a shared place and two fusion sets that list it.

**Depends on:** [MOD-021], [MOD-023], [MOD-060], [CORE-040]
**Test derivation:** Build three leaky-bucket instances composed into one builder, with their limiter places joined as a fusion set. Build the net; assert (a) only one canonical limiter place exists in the place set, (b) every transition originally referencing any of the three limiter members now references the canonical, (c) executor behavior matches a hand-written equivalent. Declare two disjoint fusion sets; assert order-independence of the built result. Declare two overlapping fusion sets; assert build is rejected. Fuse two places each consumed via `one()` by the same transition; verify the built net consumes 2 from the canonical place. Fuse places whose colliding input arcs cannot merge; verify build rejection names the fusion set. Declare `b` terminal and fuse `{a, b}`; verify `a` is terminal in the built net."#
