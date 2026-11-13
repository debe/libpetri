import Libpetri.Spec.Text

requirement_text IO_007
  id "IO-007"
  title "requiredCount and consumptionCount Contract"
  priority MUST
  kind F
  body r#"Every input cardinality variant exposes two functions:
- `requiredCount()` — the minimum number of (matching) tokens needed for enablement
- `consumptionCount(available)` — the actual number of tokens consumed during firing, given `available` tokens

⟦s1|The required count *shall* be 1 for `One` and `All`, `n` for `Exactly(n)` and `m` for `AtLeast(m)`.⟧

⟦s2|*While* `available` is at least the required count, `consumptionCount(available)` *shall* return 1 for `One`, `n` for `Exactly(n)` and `available` for `All` and `AtLeast(m)`.⟧

⟦s3|*If* `consumptionCount(available)` is called with `available` less than the required count, *then* the call *shall* fail with an error.⟧

| Variant    | requiredCount() | consumptionCount(available) |
|------------|-----------------|------------------------------|
| One        | 1               | 1                            |
| Exactly(n) | n               | n                            |
| All        | 1               | available                    |
| AtLeast(m) | m               | available                    |

**Acceptance Criteria:**
1. Each variant returns the values shown in the table.
2. Calling consumptionCount with insufficient tokens is an error.

**Test derivation:** Verify table for each variant with various available counts."#
