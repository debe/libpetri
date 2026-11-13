import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.NU_051_carrier
import Libpetri.Spec.Text.NU_051

runtime_defect RD_27
  title "Rust ignores a carrier declaration it cannot resolve, outside Route B"
  requirements r#"NU-051 (the carrier bullet: a declared carrier that is not a place of the net
is refused, in either fragment mode and whatever the query; ruling D95 (a))."#
  runtimes r#"Rust, Python (which runs the Rust verifier)."#
  defect r#"Rust checks the declared carriers only under EXTENDED and only inside Route B
(`rust/libpetri-verification/src/nu_scg_verifier.rs`, `verify_name_scg`, which answers
`Unknown` naming the place). An absent carrier is therefore silently ignored in three cases:
under BASE; under EXTENDED on a call that does not reach Route B; and under EXTENDED on a
bounded quiescence query that does reach it, because the pipeline drops the Route B `Unknown`
there and defers to Route A (`defer_to_route_a` in `SmtVerifier::verify_net`,
`rust/libpetri-verification/src/smt_verifier.rs`), whose `build_plan` skips a carrier it cannot
resolve (`rust/libpetri-verification/src/name_coloured_encoder.rs`). The open-net route
(`verify_open_net` with a `configure_smt` hook) refuses an unknown mint but ignores an unknown
carrier as well, and the doc comments promised more than Rust checked. Java and TypeScript
reject the declaration in both modes (`SmtVerifier.carrierPlaces`)."#
  evidence r#"⟪NU_051_carrier_forbids_routeBOnly⟫ (BASE) and
⟪NU_051_carrier_forbids_routeADeferral⟫ (EXTENDED) in `NU_051_carrier.lean`: the shape Rust
ships answers `Proven` on the co-mint net with the mistyped carrier `7`."#
  fix r#"`SmtVerifier::verify` judges the carrier declaration on the caller's net before any
rewrite or route and answers `Unknown` with `declared carrier place 'x' not in the net (NU-051)`
in both modes; `encode_scripts` panics with the same reason, and `verify_open_net` refuses before
either route. Python's `encode_smt_scripts` raises `ValueError` with it. Rust
`mint_declarations.rs` `nu_051_an_unknown_carrier_is_refused_in_both_modes_on_every_route`,
`nu_051_encode_scripts_panics_for_a_carrier_not_in_the_net` and
`nu_051_verify_open_net_answers_unknown_for_a_carrier_not_in_the_net`; Python
`test_nu_mint_contract.py::test_nu_051_an_unknown_carrier_is_refused_in_both_modes` and
`::test_nu_051_encode_smt_scripts_rejects_a_carrier_not_in_the_net`."#
  status "fixed, unreleased"
