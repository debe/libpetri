import Libpetri.Spec.Text

requirement_text NU_051
  id "NU-051"
  title "EXTENDED Coloured-Consumer Fragment"
  priority MAY
  kind F
  body r#"The [NU-050] Route B name-partition quotient decides the **mint → matched-join**
fragment exactly. An opt-in **EXTENDED** fragment mode widens that exact path to
two further shapes without weakening its soundness: a **coloured consumer**
(drain/relay) that removes a correlation name without a match, and **carrier
places** that thread a fork-minted name through intermediate places to a ν-join
input. The mode is a two-value knob — **BASE** (default) reproduces the shipped
mint → matched-join fragment exactly; **EXTENDED** is selected on the verifier
builder (`fragmentMode` / `fragment_mode`). Both are decided by the solver-free
Route B quotient, and by Route A where [NU-053] is offered; neither changes the canonical name-partition key
format ([VER-012]), so cross-language byte compatibility is preserved.

- **Coloured consumer (drain/relay).** Under EXTENDED, a transition with **no** match spec MAY
  consume a coloured place. The analyzer admits it only as a drain/relay role and only when it
  consumes **exactly one** coloured input at count **exactly one** ([IO-001] `One` or [IO-002]
  `Exactly(1)`). ⟦s1|*While* the fragment mode is BASE, the fragment classifier *shall* give no role
  to a transition without a match spec that consumes a coloured place.⟧ ⟦s2|*While* the fragment mode
  is EXTENDED, *if* a transition without a match spec consumes exactly one coloured input, at
  count one, has no reset, read or inhibitor arc on a coloured place, puts on each branch
  exactly one token, and never a drained batch, into each coloured place the branch writes, and
  on timeout writes a coloured place only by forwarding that input, *then* the fragment
  classifier *shall* give it the coloured-consumer role of that input's place, whether or not it
  is declared a mint.⟧ A coloured consumer **relays** the consumed name-symbol into each coloured
  output of the fired branch (threading the same name), or **drains** it (dead-letters the name)
  on a branch that produces no coloured output; a single `Xor` transition ([IO-012]) MAY relay
  on one branch and drain on another. ⟦s3|*When* a coloured consumer fires on a branch with a name
  its coloured input holds, the name layer *shall* remove one token of that name from the input,
  add one token of that name to each coloured output of the branch and change no other count, so
  a branch with no coloured output drains the name.⟧ Because the consumed count is fixed at one,
  the role is identified by the input place name alone — no count, no input list. A consumer
  that consumes more than one coloured place, or consumes at any count other than one
  (`Exactly(n≥2)`, `AtLeast`, `All`), is **rejected** to the sound over-approximation: the base
  marking adds exactly one token per output place, so re-emitting a higher input cardinality
  into the name layer would over-count and could let a join fire by equating two distinct names
  (a false `Proven`). ⟦s4|*While* the fragment mode is EXTENDED, the fragment classifier *shall*
  give a transition without a match spec that consumes a coloured place no role other than the
  coloured-consumer role of its one coloured input, and that role only when it consumes exactly
  one coloured input, at count one, and puts on each branch exactly one token, and never a
  drained batch, into each coloured place the branch writes.⟧ ⟦s5|The fragment classifier *shall*
  give the coloured-consumer role to no other transition: to none while the fragment mode is
  BASE, to no matched transition and to no transition that consumes no coloured place.⟧

- **Relay/drain action precondition.** The coloured-consumer role is a modeling
  contract on the action, and MUST be documented as such. The action MUST thread
  the consumed correlation name into its coloured outputs (relay), or into **none**
  of them (drain); it MUST NOT mint a *fresh* name into a coloured output while
  consuming a coloured token. A consume-and-remint transition is **out of
  contract** for EXTENDED — the name layer would thread the consumed name where the
  runtime mints afresh, so this mode does not make such a net exact. Selecting
  EXTENDED is the declaration of this contract, and the report of a verdict names the
  consumers whose action writes it assumes. A write the executor makes on timeout is
  no action write: a timeout of a coloured consumer that writes a coloured place is a
  relay only when it forwards the consumed coloured input itself. A forward of another
  input copies a name the consumer did not consume, and an `Out.Place` writes a unit
  token with no name; either puts the net outside the fragment. ⟦s6|*If* a transition without a
  match spec consumes a coloured place and its timeout writes a coloured place other than by
  forwarding that consumed input, *then* the fragment classifier *shall* give it no role.⟧

- **Carrier places (fork-threaded co-mint).** Under EXTENDED, an author MAY declare
  intermediate **carrier** places (`carrierPlaces` / `carrier_place(s)`) that carry
  a fresh name from the minting fork ([NU-010]) onward to a ν-join input. The
  analyzer unions the declared carriers into the coloured set **before** role
  assignment, so the existing mint co-mints one fresh name into all of them.
  ⟦s7|*While* the fragment mode is EXTENDED, the fragment classifier *shall* give roles
  against the coloured set it uses with no carrier declared, with every declared
  carrier place added and no other place.⟧ In either fragment mode, a declaration
  whose carrier places are all places of the net is accepted. A
  declared carrier name absent from the net's places MUST NOT be silently ignored,
  in either fragment mode and whatever the query:
  the implementation MUST fail loudly (reject at the builder naming the offending
  place, or surface `Unknown` with a reason naming it), because a mistyped carrier would let
  two fork branches mint independent names and produce a confident, spurious
  deadlock verdict. ⟦s8|A refusal that does not depend on the carrier declaration, such as a
  stop before the call starts ([VER-013]), an unresolved property place ([VER-003]) or a
  declared mint that is not a transition of the net ([NU-010]), may come first, and that
  refusal is then the answer.⟧ ⟦s9|*If* a declared carrier place is not a place of the net, *then*
  the verifier *shall* either reject the declaration, naming such a place, or answer
  `Unknown` with a reason that names at least one such place and no other place, in
  both BASE and EXTENDED and whatever the query, unless the same request with no carrier
  place declared gets the same refusal.⟧ Under BASE, the fragment classifier
  ignores declared carriers (a documented no-op); the in-flight split of [VER-004]
  reads them in both modes.
  ⟦s10|*While* the fragment mode is BASE, the fragment classifier *shall* give roles
  against the same coloured set whatever carrier places are declared.⟧

- **Reset/read/inhibitor-on-coloured exclusion (BOTH modes).** In **both** BASE and
  EXTENDED, the analyzer rejects a net in which **any** coloured place carries a
  reset ([CORE-034]), read ([CORE-032]), or inhibitor ([CORE-031]) arc on any
  transition. Such an arc would be misclassified `Ordinary`, letting the base step
  zero or gate the coloured place while the name layer keeps the symbol, drifting
  the name layer from the base count marking. This is a deliberate soundness
  tightening applied to BASE too (rejection just falls back to the sound
  over-approximation); it never turns a `Proven`/`Violated` into an unsound verdict. ⟦s11|*If* a
  coloured place carries a reset, read or inhibitor arc of a transition, *then* the fragment
  classifier *shall* give that transition no role, in both BASE and EXTENDED.⟧

- **Off-key coloured input exclusion (BOTH modes).** In **both** BASE and EXTENDED,
  the analyzer rejects a net in which a matched transition consumes a coloured place
  through an input that is **not** one of its match keys. ⟦s12|*If* a matched transition
  consumes a coloured place through an input that is not one of its match keys, *then* the
  fragment classifier *shall* give it no role, in both BASE and EXTENDED.⟧ Such an input consumes
  FIFO ([NU-020]), whatever the token's name, so the name layer cannot know which
  name leaves the place: Route B would keep the symbol and Route A would force the
  join's shared colour on it. A non-coloured non-key input (a budget or permit) is
  unaffected. Rejection just falls back to the sound over-approximation.

- **Diagnosability.** When EXTENDED is requested but the net falls outside this
  fragment, the verifier MUST surface a short note (the "EXTENDED declined" note: a
  report line saying that the exact ν path was not taken and why, in words the
  implementation chooses) rather than silently falling back, so an author can tell the exact path was not
  taken.

**Acceptance Criteria:**
1. (MUST) Under EXTENDED, a drain/relay fixture (a non-match transition consuming
   one coloured place at count one) classifies into the coloured-consumer role;
   under BASE the same net is rejected to the over-approximation.
2. (MUST) A coloured consumer that consumes at count `Exactly(n≥2)` (or `AtLeast` /
   `All`), or consumes more than one coloured input, is rejected under EXTENDED — no
   false `Proven` from an over-counted name layer, no dropped base-enabled firing.
3. (MUST) In both BASE and EXTENDED, a net with a reset, read, or inhibitor arc on a
   coloured place is rejected (returns no fragment).
4. (MUST) In both BASE and EXTENDED and whatever the query, a declared carrier place
   not present in the net fails loudly (builder rejection naming the place, or `Unknown`
   with a reason naming the place), unless a refusal that does not depend on the declaration
   is the answer; it is never silently ignored.
5. (SHOULD) With carriers declared, an end-to-end quiescence property (deadlock-free
   / joined-or-dead-lettered) is decided exactly via Route B — it PROVES on a
   fork-threaded co-mint plus drain fixture and reports VIOLATED when the drain is
   removed, and the verdict is attributable to Route B (the report names the
   name-partition quotient), not the name-blind SMT path.
6. (MAY) A single `Xor` coloured consumer relays the name on one branch and drains
   it on another through the same transition.
7. (MUST) In both BASE and EXTENDED, a matched transition that consumes a coloured
   place through a non-key input is rejected (returns no fragment, no coloured plan),
   and a stranding such a net can reach is not reported `Proven`.
8. (MUST) Under EXTENDED, a coloured consumer whose timeout forwards another input, or
   writes a unit token, into a coloured place is rejected on both routes. With
   `m1: budget → A1`, `m2: budget → A2` minting, `r1: A1, reqA → xor(okA, timeout(20,
   forwardInput(reqA, KA)))`, its twin `r2` into `KB` and a join on `KA`, `KB`, the
   executor reaches `done` when both requests carry one id, and `placeBound(done, 0)` is
   not `Proven`. A consumer whose timeout forwards its coloured input is still a relay.

**Depends on:** [NU-050], [VER-012], [NU-020]
**Test derivation:** `classify` accepts a drain/relay fixture under EXTENDED and
rejects it under BASE; an `Exactly(2)` coloured consumer is rejected (blocker-1 /
blocker-2 regression); a reset-on-coloured net is rejected in both modes; an unknown
carrier name fails loudly in both modes; a join consuming another join's key off-key is rejected in
both modes and its reachable stranding is not proven; an end-to-end `deadlockFree` / `JoinedOrDeadLettered`
query on a fork-threaded co-mint plus drain fixture PROVES via Route B and turns
VIOLATED when the drain is removed."#
