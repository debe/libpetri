import Libpetri.Spec.Text

requirement_text MOD_013
  id "MOD-013"
  title "Nested Instantiation (prefix concatenation associative)"
  priority MUST
  kind F
  body r#"A subnet that itself composes other subnets can be instantiated like any other subnet: the third sentence below makes `instantiate` accept it. The runtimes build such a subnet definition with `fromNet` ([MOD-014]) over a net that composes an instance ([MOD-020]). The resulting nested names use `"/"` as the separator at every level: `outer/inner/originalName`.

Prefix concatenation is associative on names: instantiating a subnet `S` (which internally composes an instance `inner` of subnet `T`) with prefix `outer` gives the name `outer/inner/x` for every place `x` of `T` that the body of `S` holds as `inner/x`, and `outer/inner/x` is `x` renamed under the concatenated prefix `outer/inner`. So the nested names are the names of `T` that the body of `S` holds, renamed under `outer/inner`. No single `instantiate` call produces them, because `outer/inner` contains `/` and is not a valid prefix ([MOD-010]).

Which places and transitions of `T` the body of `S` holds is decided by the composition. A port place of `T` that `S` binds to a place of its own is replaced by that place and does not become `outer/inner/x` ([MOD-020]). An internal place of `T` that no arc names is not added by the composition ([MOD-020]). A transition of `T` merged with a caller transition through a channel takes the caller's name ([MOD-021]).

⟦s1|*When* the body of a subnet definition `S` holds the place `i/x` of an instance under prefix `i` of a subnet definition `T`, for a place `x` of `T`, and `S` is instantiated with prefix `o`, the instance *shall* hold the place `o/i/x`.⟧

⟦s2|*When* the body of a subnet definition `S` holds the transition `i/t` of an instance under prefix `i` of a subnet definition `T`, for a transition `t` of `T`, and `S` is instantiated with prefix `o`, the instance *shall* hold the transition `o/i/t`.⟧

⟦s3|*When* `instantiate` is given a non-empty prefix that contains no `/` and the body of the subnet definition declares no terminal place, `instantiate` *shall* succeed, also when names of the body contain `/` because the body holds a composed instance.⟧

These sentences say what the instance holds. That it holds nothing more, so that the names of the form `outer/inner/x` are exactly the names `inner/x` of the body renamed under `outer`, follows from [MOD-010]: the renamed body holds exactly the body's places and transitions, each renamed. The third sentence takes for granted that every port of the definition names a place of its body and every channel a transition of its body, which the subnet builder ([MOD-006]) and `fromNet` ([MOD-014]) check.

**Acceptance Criteria:**
1. A subnet `S` containing a composed instance of `T` (instantiated with prefix `inner`), instantiated with prefix `outer`, produces names of the form `outer/inner/<original>`.
2. The names of the form `outer/inner/x` in the doubly-prefixed instantiation are exactly the names `inner/x` that the body of `S` holds, each renamed under `outer`, which is `x` renamed under the concatenated prefix `outer/inner`. An instantiation of `T` with the prefix `outer/inner` itself is rejected ([MOD-010]).
3. Per-instance state isolation per [MOD-012] holds at every nesting level.

**Depends on:** [MOD-010], [MOD-012], [MOD-014], [MOD-020], [MOD-021]
**Test derivation:** Build subnet `T` with internal place `x`. Build subnet `S` that composes `T` instance with prefix `inner`. Instantiate `S` with prefix `outer`; verify `outer/inner/x` is among the renamed place names."#
