import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.CORE_043

runtime_defect RD_47
  title "A reused Java `SmtVerifier` checks the net its previous call rewrote"
  requirements r#"CORE-043 (line 3: a verification entry point fails exactly when compiling the
submitted net does)."#
  runtimes r#"Java."#
  defect r#"the CORE-043 check before `prepare()` read the mutable `net` field (`pipeline` and
`encodeScripts` in `java/src/main/java/org/libpetri/smt/SmtVerifier.java`), which the previous
call left rewritten. A second call therefore threw when the first call's rewrite had made a
CORE-043 violation, the case of RD-08 (a passthrough sink split under `CONFLICT`), for example on
`encodeScripts()` called twice. The read outside the synchronized `prepare()` was also a data race
when threads share a verifier."#
  evidence r#"none; the CORE_043 assumes record it, as for RD-08."#
  fix r#"`pipeline()` and `encodeScripts()` run the check on the caller's net (`callerNet`), with
the RD-08 change. Java `SplitDemandTest.CORE043_aReusedVerifierChecksTheCallersNet`."#
  status "fixed, unreleased"
