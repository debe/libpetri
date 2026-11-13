import Libpetri.Spec.Text

requirement_text MOD_012
  id "MOD-012"
  title "Per-Instance State Isolation"
  priority MUST
  kind B
  body r#"The private runtime state of each module instance is independent of every other instance. ⟦s1|A place of an instance is **private** to it when no port binding names it, as the caller place or as the port place the binding replaces ([MOD-020]), no fusion set lists it ([MOD-060]), no transition of the instance that a channel binding merges names it ([MOD-021]), and no transition outside the instance names it: no hand-added transition, no caller-side definition of a channel binding, no transition of another instance and no directly composed subnet ([MOD-025]).⟧ ⟦s2|An auto-composition ([MOD-024]) of an instance under prefix `q` counts as binding a place `x` when `x` is the unrenamed place of one of that instance's ports or when `q/x` is a place of that instance, whether or not the call binds it.⟧ ⟦s3|Port bindings, channels and fusion sets are how instances share state on purpose, so isolation covers private places only.⟧

⟦s4|After composition into a flat net, private places of two distinct instances MUST occupy distinct slots in the compiled net's place index, hold disjoint token bags, and evolve independently under the executor.⟧

⟦s5|This isolation is a structural consequence of name-prefixing per [MOD-010] (distinct prefixed names → distinct place identities → distinct slots).⟧ ⟦s6|No additional runtime mechanism is required.⟧

⟦s7|Private place token state, the enablement state of a transition whose arc places are all private, and the timing clock of such a transition (per [TIME-010], [TIME-011]) MUST all be per-instance.⟧

⟦s8|In the sentences below, `a` and `b` are single-segment prefixes: non-empty and without `/` ([MOD-010]).⟧ ⟦s9|For two instances nested in one outer instance ([MOD-013]), the sentences apply to the build of the outer subnet's body, where their prefixes are single segments.⟧

⟦s10|*When* a net is built by composition, each of its transitions that names a place private to the instance under prefix `b` *shall* have a name of the form `b/x`.⟧

⟦s11|*When* a transition whose name has the form `a/x` fires in a net built by composition, every place private to the instance under another prefix `b` *shall* keep its token count.⟧

⟦s12|*When* a `compose(instance, bindings)` call ([MOD-020]) adds a transition of the instance under prefix `b` that names a place private to that instance, the built net *shall* hold a transition of the same name that names that place.⟧

⟦s13|*When* a transition whose name has the form `a/x` fires in a net built by composition, each transition named `b/y`, for another prefix `b`, whose arc places are all private to the instance under `b` *shall* keep its enablement and its armed state, and its stamp if it is armed.⟧

⟦s14|*When* a transition whose name has the form `a/x` is reaped, or the firing clock advances in a net that holds such a transition, each transition named `b/y`, for another prefix `b`, *shall* keep its armed state and its stamp.⟧

**Acceptance Criteria:**
1. Compose two instances of the same subnet definition (different prefixes) into one net; build and execute. Tokens added to instance A's private place do not appear in instance B's corresponding private place.
2. Firing a transition in instance A does not affect the enablement of a transition in instance B whose arc places are all private to B.
3. Firing a transition in instance A does not change the timing clock of a transition in instance B whose arc places are all private to B; reaping a transition of A, or advancing the clock, changes no timing clock in B.
4. Compose three instances A, B and C of one subnet definition and fuse a caller place with a place of C; after build, each transition of A and of B still names its own private places.

**Depends on:** [MOD-010], [MOD-020], [MOD-021], [MOD-024], [MOD-025], [MOD-060], [CORE-070], [TIME-010], [TIME-011], [TIME-012], [TIME-013]
**Test derivation:** Build a bounded-buffer subnet; compose two instances `b1` and `b2`; add tokens to `b1/slots`; verify `b2/slots` token count unchanged."#
