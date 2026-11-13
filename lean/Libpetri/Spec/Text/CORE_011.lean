import Libpetri.Spec.Text

requirement_text CORE_011
  id "CORE-011"
  title "Token Creation"
  priority MUST
  kind F
  body r#"A host creates a token through a factory; a Python host passes values instead, and the Rust runtime it binds creates their tokens. The default factory stamps the token with the current reading of the host's wall clock. It is called from host code, which no executor's clock reaches, so a clock injected into an executor ([TIME-015]) does not change what it stamps. A second factory takes the timestamp as an argument and keeps it as given, without clamping or rounding it, so that a host can create a token that is the same on every replay or restore one from a snapshot ([CORE-073]); this is the construction at an explicit timestamp that [TIME-015] requires. A helper that seeds a token from a clock's reading is this second factory applied to that reading. The canonical unit token ([CORE-012]) carries the timestamp 0, the start of the epoch. A token the executor creates (an action output written as a value, a token injected as a raw value, the unit token of a timeout outcome) is not made by these factories: it is stamped from the executor's epoch clock ([TIME-015] AC13), and a forwarded token keeps its timestamp ([IO-014]). A token an action builds itself through a factory and outputs as a token (Java, TypeScript) keeps that factory's stamp.

⟦s1|*When* a host creates a token from a value through the default factory, the token *shall* hold that value and carry the reading of the host's wall clock at the call as its creation timestamp, whatever clock an executor runs on ([TIME-015]).⟧

⟦s2|*When* a host creates a token from a value and a timestamp through the explicit-timestamp factory, the token *shall* hold that value and carry that timestamp, whatever the clocks read at the call.⟧

⟦s3|*When* a host creates the canonical unit token, the token *shall* hold no value and carry the timestamp 0, whatever the clocks read at the call.⟧

⟦s4|*When* an action writes a value to an output place, the token the executor creates for it *shall* hold that value and carry the reading of its epoch clock at the write ([TIME-015]).⟧

A Python action's `ctx.output` only buffers the value: its write is made when the action returns or calls `ctx.flush()`, and its token carries the epoch clock's reading at that point.

⟦s5|*When* a host injects a raw value into an environment place, the token the executor creates for it *shall* hold that value and carry the reading of its epoch clock at the call ([TIME-015]).⟧

⟦s6|*When* the budget of a firing runs out, each token the executor mints for the timeout outcome *shall* carry the reading of its epoch clock at that moment, and each token a `ForwardInput` forwards *shall* be the consumed token itself, with its timestamp ([IO-014]).⟧

⟦s7|*When* an action outputs a token it built itself, or a host injects a token it built, the executor *shall* keep that token as it is, with its timestamp.⟧

**Acceptance Criteria:**
1. Creating a token through the default factory yields a token that holds the given value and records the current reading of the host's wall clock.
2. While the host's wall clock does not go back, two tokens created one after the other through the default factory have non-decreasing timestamps.
3. A token created at an explicit timestamp holds the given value and carries that timestamp unchanged, also when the timestamp lies before the epoch or is finer than a millisecond and the implementation's timestamp type can hold it.
4. The canonical unit token holds no value and carries the timestamp 0.
5. While an executor runs on an injected clock, a token created through the default factory carries the reading of the host's wall clock, not the injected clock's.
6. While an executor runs on an injected clock, a token it creates for an action's value write, for a raw-value injection or as a minted timeout output carries the epoch clock's reading at that moment, not the wall clock's; a forwarded token, a token the action built and a token the host built keep their timestamps.

**Test derivation:** Read the host's wall clock, create a token through the default factory and read the wall clock again; verify that the token holds the given value and that its timestamp lies between the two readings. Create two tokens in sequence through the default factory; verify second timestamp >= first. Repeat the first step while an executor runs on an injected clock that reads far from the wall clock; verify that the timestamp still lies between the two wall-clock readings. Create tokens at explicit timestamps, including one before the epoch and one finer than a millisecond where the timestamp type can hold them, and the canonical unit token; verify that each token holds its value (no value for the unit token) and carries its timestamp unchanged (0 for the unit token). Run an executor on an injected clock that reads far from the wall clock: let an action write a value and output a token it built at an explicit timestamp, inject a raw value and a token built at an explicit timestamp, move the clock, and let a firing whose timeout branch mints a unit token and forwards its input time out; verify that the written value, the injected value and the minted unit token carry the injected clock's readings at their steps, and that the forwarded and the built tokens keep their timestamps."#
