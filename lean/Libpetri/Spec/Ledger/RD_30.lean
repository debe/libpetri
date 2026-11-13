import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.MOD_031
import Libpetri.Spec.Text.MOD_031

runtime_defect RD_30
  title "The Python binding adapter resolves the given name before the correspondence"
  requirements r#"MOD-031 (an action's context operations resolve a declared place through the
correspondence, and a binding adapter that resolves for its actions keeps the same order)."#
  runtimes r#"Python."#
  defect r#"`require_output` and `resolve_lookup_key` first look the given name up in the
allowed outputs or in the delivered input or read map, and fall back through `local_name_map`
only when that fails (`rust/libpetri-py/src/action.rs`). When the given name is itself
a place of the call's kind that the correspondence resolves to another place (a port `a` bound
to the caller place `b`, and a port `b` bound to `c`), the call answers for the given place,
not for the place the correspondence names. Java and TypeScript resolve first; the Rust native
context hands the correspondence to native actions."#
  evidence r#"⟪MOD_031_ctx_mutant_literalFirst_killed⟫ and ⟪mod031ctx_collision⟫ in
`MOD_031.lean`: on the collision example the name-first lookup answers for the wrong place."#
  fix r#"the adapter resolves the given name through the correspondence first and looks up only
the resolved name; its error messages still name the given name. Python
`test_subnet_local_names.py::test_correspondence_resolves_before_the_given_name_mod031` (`[input]`
and `[read]`) and `::test_output_resolves_before_the_given_name_mod031`."#
  status "fixed, unreleased"
