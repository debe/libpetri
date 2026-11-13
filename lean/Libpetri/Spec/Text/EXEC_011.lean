import Libpetri.Spec.Text

requirement_text EXEC_011
  id "EXEC-011"
  title "~~Guarded Token Consumption~~ (Removed)"
  status Removed
  body r#"Guarded consumption was removed together with the guard predicate itself (see
[IO-006]). With no per-token value predicate in the input specification, token
selection is purely positional: [EXEC-010] (FIFO order) and [IO-007]
(`consumptionCount`) fully determine which tokens a firing consumes. The one
remaining per-token selection rule is the ν-name correlation of [NU-020], which is
specified there and is structural, not a value predicate.

Retained as a tombstone for traceability; excluded from the active requirement count."#
