import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.NU_010_ac6
import Libpetri.Spec.Text.NU_010

runtime_defect RD_38
  title "Rust verification checks the mint declaration against its own rewritten net"
  requirements r#"NU-010 (the declared-mint bullet: a declared mint that is not a transition of
the net is refused, with the same reason naming it at every entry point; AC6)."#
  runtimes r#"Rust, Python (which runs the Rust verifier)."#
  defect r#"`SmtVerifier::verify` checks the declared mints
(`name_fragment::unknown_mint_reason(self.net, ...)`,
`rust/libpetri-verification/src/smt_verifier.rs`) inside `verify_net`, after the
verifier's own rewrites: the `Arrivals(k)` closure (`with_arrivals`, called from `verify`), the
inert places, the in-flight split and the terminal rewrite (`verify_terminals_split`). Those
rewrites add transitions such as `complete:<t>` (`completion_transition`,
`rust/libpetri-verification/src/in_flight.rs`) and `env:arrive[i]:<p>` (`close_open_net`,
`rust/libpetri-verification/src/open_net/closure.rs`), so a
declaration naming one of them is accepted and verification answers a verdict. Every other
entry point checks the caller's net and refuses the same request with
`declared mint transition 'complete:t' not in the net (NU-010)`: Rust `encode_scripts`
(`smt_verifier.rs`, before `with_arrivals`), Python `encode_smt_scripts`
(`py_encode_smt_scripts`, `rust/libpetri-py/src/verification.rs`), Java at declaration
(`SmtVerifier.mintTransitions`, `java/src/main/java/org/libpetri/smt/SmtVerifier.java`)
and TypeScript at declaration and in `encodeScripts`
(`mintTransitions` and `encodeScripts`, `typescript/src/verification/smt-verifier.ts`, both on
`callerNet`). Rust's own docs promise the same answer (`encode_scripts` panics "with the reason
verify answers Unknown with"; the doc comment of `unknown_mint_reason` in `name_fragment.rs`). The fix is to run the check on the caller's net before
`with_arrivals`, as `encode_scripts` does. Open-net verification is not affected: all three
runtimes check its declaration on the closed net."#
  evidence r#"⟪NU_010_unknownMint_forbids_rewrittenNet⟫ (`NU_010_ac6.lean`): an entry
point that checks the names against the caller's transitions plus `complete:t` answers
`Violated` on `p0 -> t -> p1` with `complete:t` declared, where the reference script encoding
fails with the NU-010 reason (⟪nu010_rewritten_vs_encode⟫)."#
  fix r#"`verify` judges the mint declaration on the caller's net before the `Arrivals` closure
and the other rewrites, as `encode_scripts` does, so `complete:t` and `env:arrive[0]:p0` are
refused with the NU-010 reason. Rust `mint_declarations.rs`
`nu_010_ac6_mint_naming_a_rewrite_added_transition_is_refused`; Python
`test_nu_mint_contract.py::test_nu_010_ac6_mint_naming_a_rewrite_added_transition_is_refused`."#
  status "fixed, unreleased"
