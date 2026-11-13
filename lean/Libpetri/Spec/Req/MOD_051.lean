import Libpetri.Spec.Registry
import Libpetri.Spec.Req.VER_006
import Libpetri.Spec.Req.CORE_042
import Libpetri.Reference.ComposeBuild
import Libpetri.Reference.ComposeDef

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# MOD-051: `SubnetDef.verify(harness)` for local property verification (`spec/11-modular-composition.md`)

A subnet definition is verified on its own: `verify` wraps it in a **synthetic net** and runs the
standard verifier once per property of the harness. Two blocks:

* `MOD_051` (B): the verification operation. Over an instantiation function `Inst` ([MOD-010]),
  a build-script function `BS` ([MOD-023]), the compile check `C` of [CORE-043], an
  environment-aware decider `D` ([VER-006]) and the operation itself `SV`:
  1. a harness without a token source for an input or in-out port is refused;
  2. a result's synthetic net is what a new enclosing builder builds from one call: the instance
     under the prefix `sut`, each port bound to its harness place (`harness_in_<port>`,
     `harness_out_<port>`, `harness_io_<port>`), no channel bound, nothing else; so a call whose
     instance or synthetic net does not build fails (`mod051_fails_of_build`);
  3. a synthetic net the [CORE-043] check refuses is refused, naming the same transition, with
     or without properties;
  4. the result holds, for each property of the harness, `D` on the synthetic net, set up with
     the property, the harness places of the input and in-out ports as environment places, the
     selected mode, the default options and the empty marking, then passed through the hook;
  5. `verify` without options is `verify` under `AlwaysAvailable` with no hook.
* `MOD_051_bind` (F): `bindActions` on a definition is the net-level binding of [CORE-042] on the
  body, keyed by the body's own (unprefixed) names; name, ports, channels and place
  correspondences are kept.

That `verify` returns a result at all when nothing is refused is the coverage condition
`Mod051Covers`, never a line (the convention of `GlossaryExec.lean`): the reference meets it
(`mod051_ref_covers`) and an operation that refuses every call is killed there
(`mod051_rejectAll_not_covers`).

The witnesses are `refVerifySubnet Inst BS C D`, for every choice of the four parts, and
`refDefBind` with the map read as Rust reads it (`refDefBindMapKeep`) or as Java and TypeScript
read it (`refDefBindMapClobber`). The worked example is the forwarding subnet `fwd` (input port
`in` over `IN`, transition `work` from `IN` to `OUT`, output port `out` over `OUT`), whose
synthetic net is `harness_in_in → sut/work → harness_out_out`: VER-006's `env IN → T → OUT`,
renamed.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam Libpetri.Spec.Verifier

/-! ## The model -/

section Model

variable {A : Type}

/-- **The harness place of a port**: `harness_in_<port>` for an input port, `harness_out_<port>`
for an output port, `harness_io_<port>` for an in-out port (Rust `harness.rs`, Java
`SubnetDef.java`, TypeScript `subnet-def.ts` alike). -/
def harnessPlace (q : Port String) : String :=
  match q.dir with
  | .input => "harness_in_" ++ q.name
  | .output => "harness_out_" ++ q.name
  | .inout => "harness_io_" ++ q.name

/-- **The synthetic script**: one compose call on a new enclosing builder, the instance `I` with
every port of `S` bound to its harness place and no channel bound. -/
def synthScript (S : SubnetDef String A) (I : Instance String A) : List (Op String A) :=
  [.compose I (S.ports.map fun q => (q.name, harnessPlace q)) []]

/-- **The harness's environment places**: the harness places of the input and in-out ports, in
port order. -/
def harnessEnvs (S : SubnetDef String A) : List String :=
  (S.ports.filter fun q => q.dir != .output).map harnessPlace

/-- **A harness**: the ports it supplies a token source for (by name) and the properties to check
([VER-002]). The parameter value is checked by the host language and not modelled. -/
structure SubnetHarness where
  /-- The names of the ports the harness supplies a token source for. -/
  sources : List String
  /-- The properties to check. -/
  props   : List (VerProp String)

/-- Every input and in-out port of `S` has a token source in `h`. -/
def sourcesOk (S : SubnetDef String A) (h : SubnetHarness) : Bool :=
  S.ports.all fun q => q.dir == .output || h.sources.contains q.name

/-- The empty initial marking, the verifier's default. -/
def emptyNM : NMarking String := ⟨[], by decide, by decide⟩

/-- **The setup of one per-property verifier**: the property, the registered environment places,
the environment mode, the options and the initial marking. -/
structure VerifySetup where
  /-- The property. -/
  prop : VerProp String
  /-- The registered environment places. -/
  envs : List String
  /-- The environment mode ([VER-006]). -/
  mode : EnvMode
  /-- The verifier options. -/
  opts : Options
  /-- The initial marking. -/
  m0   : NMarking String

/-- **The options of `verify`**: the environment mode and the configure hook, which receives the
synthetic net and the setup and returns the setup to run. -/
structure SubnetVerifyOpts (A : Type) where
  /-- The environment mode. -/
  mode : EnvMode
  /-- The configure hook. -/
  hook : ComposedNet String A → VerifySetup → VerifySetup

/-- `AlwaysAvailable` and no hook (the hook that returns the setup unchanged). -/
def defaultVerifyOpts : SubnetVerifyOpts A := ⟨.always, fun _ s => s⟩

/-- **What `verify` returns**: the synthetic net and one entry per property. -/
structure SubnetReport (A : Type) where
  /-- The synthetic net. -/
  synth   : ComposedNet String A
  /-- The entries: a property and the verifier's result for it. -/
  results : List (VerProp String × Result String)

/-- **A subnet verification operation**: a definition, a harness and the options (`none`: the
call without options) give a report, or fail with a message. -/
abbrev SubnetVerifyFn (A : Type) : Type :=
  SubnetDef String A → SubnetHarness → Option (SubnetVerifyOpts A) →
    Except String (SubnetReport A)

/-- **One per-property verification**: the setup (the property, the environment places `envs`,
the mode of `o`, the default options, the empty marking) passed through the hook, then the
decider on the synthetic net. -/
def verifyOne (D : EnvDecider String) (o : SubnetVerifyOpts A) (c : ComposedNet String A)
    (envs : List String) (φ : VerProp String) : Result String :=
  let s := o.hook c ⟨φ, envs, o.mode, {}, emptyNM⟩
  D s.mode s.envs s.opts (c.toTimed 0) s.prop s.m0

/-- The [CORE-043] refusal of `verify`, naming the transition (the wording is kind Q). -/
def core043VerifyMsg (n : String) : String :=
  "transition '" ++ n ++ "' declares an output spec and carries passthrough (CORE-043)"

/-- The refusal of a harness without a token source for an input or in-out port (kind Q). -/
def missingSourceMsg : String :=
  "verify: the harness is missing a token source for an input or in-out port (MOD-051)"

/-- **The reference `verify`**: refuse a harness without every token source; instantiate under
`sut`; build the synthetic script; refuse a net the [CORE-043] check refuses; otherwise one entry
per property, `verifyOne` with the harness's environment places and the options given (or the
default). -/
def refVerifySubnet (Inst : InstFn String A) (BS : ScriptFn String A)
    (C : BuiltNet String A → Option String) (D : EnvDecider String) : SubnetVerifyFn A :=
  fun S h o? =>
    let o := o?.getD defaultVerifyOpts
    if sourcesOk S h then
      match Inst S "sut" with
      | .error m => .error m
      | .ok I =>
        match BS (synthScript S I) with
        | .error m => .error m
        | .ok c =>
          match C c.toBuiltNet with
          | some n => .error (core043VerifyMsg n)
          | none => .ok ⟨c, h.props.map fun φ => (φ, verifyOne D o c (harnessEnvs S) φ)⟩
    else .error missingSourceMsg

/- The reference `verify` is the witness model of MOD-051. -/
#spec_witness refVerifySubnet

end Model

/-! ## MOD-051 (B): the verification operation -/

requirement MOD_051
  id "MOD-051"
  title "SubnetDef.verify(harness) for local property verification"
  kind B
  scope "verify on a subnet definition in Java, TypeScript and Rust, and verify_subnet in Python (on the Rust one); SHOULD, so the shall sentences bind an implementation that offers it"
  source verbatim "spec/11-modular-composition.md"
  quote "*When* `verify` returns a result, the synthetic net it verified *shall* be the net that a new enclosing builder builds from one call that composes the subnet's instance under the prefix `sut`, binds each port to its harness place (`harness_in_<port>` for an input port, `harness_out_<port>` for an output port, `harness_io_<port>` for an in-out port), binds no channel and declares nothing else."
        "*If* instantiating the subnet under the prefix `sut` fails or building the synthetic net fails, *then* `verify` *shall* fail."
        "*If* the harness supplies no token source for an input or in-out port of the subnet, *then* `verify` *shall* fail and *shall* return no verification result."
        "*If* the harness supplies a token source for every input and in-out port and the [CORE-043] check fails on the synthetic net, *then* `verify` *shall* fail with an error that names the transition the check names, also when the harness lists no property."
        "*When* `verify` returns a result, the result *shall* hold an entry for each property of the harness and no entry for another property, and each entry for a property *shall* be the result of the standard verifier ([VER-003], [VER-006]) on the synthetic net, set up with that property, the harness places of the input and in-out ports as environment places, the selected environment mode, the verifier's default options and the empty initial marking, and then passed, together with the synthetic net, through the configure hook, whose changes override that setup."
        "*When* `verify` is called without options, it *shall* verify under the environment mode `AlwaysAvailable` with no configure hook."
  reading "For every instantiation function Inst, build-script function BS, CORE-043 compile check C, environment-aware decider D and verification operation SV, over every definition S, harness h and options:"
          "if some input or in-out port of S has no token source in h, SV fails;"
          "if SV returns a report r, then Inst instantiates S under the prefix sut as some instance I, and BS builds r's synthetic net from the one call that composes I with every port bound to its harness place and no channel bound (so SV fails when Inst or BS fails);"
          "if every input and in-out port has a token source, Inst instantiates S under sut as I, BS builds the synthetic script of I as c and C refuses c naming n, then SV fails with a message that names n, whatever properties h lists;"
          "if SV with options o returns a report r, then for one list envs that is a permutation of the harness places of the input and in-out ports, every entry of r is (φ, verifyOne D o r.synth envs φ) for a property φ of h, and every property of h has an entry;"
          "SV without options is SV with the options AlwaysAvailable and the hook that changes nothing."
  assumes "SV is the subnet verification of one implementation, read as a function: Rust verify_subnet_with_options (rust/libpetri-verification/src/harness.rs:356-447), Java SubnetDef.verify (java/src/main/java/org/libpetri/core/SubnetDef.java:282-380), TypeScript SubnetDef.verify (in typescript/src/core/subnet-def.ts), Python verify_subnet (py_verify_subnet in rust/libpetri-py/src/verification.rs, on the Rust one). Failing is a panic or an exception, read as an error; the shorter signatures (verify(harness), verify(harness, mode)) are SV with no options and with the options of that mode and no hook. Places are names (String). The parameter value (item 1) is type-checked by the host language and not modelled (MOD-010 AC4), and neither are token types: Java gives each harness place its port place's token type (SubnetDef.java newSyntheticPlace), Rust and TypeScript key places by name, and no MOD-022 type check can fire on a fresh harness place."
          "Line 1 is item 2 and AC3 as reworded under ruling R-MC9 (a), carried by D20: the environment mode of item 4 bounds the input, not the token source. Every runtime calls the source once while it builds the synthetic net and discards the token (harness.rs:39-48, :389-393 and :416, SubnetDef.java:311-313 and :332-334, subnet-def.ts:295-301 and :320-326), so a source carries no count the verifier reads and does not set the harness place's token type either (Java takes it from the port's own place, TypeScript makes an untyped place, Rust keys the place by name); what the line keeps is that a missing source for an input or in-out port is an error. The harness models a source by its port name only, so item 2's 'a source that fails or returns no token makes verify fail' (a panic in Rust, an exception or a null or undefined check in Java and TypeScript) is the host language's and not modelled (harness.rs:380-388 and :407-415, SubnetDef.java:302-309 and :325-331, subnet-def.ts:284-292 and :312-319). A source for an output port or for a name no port has is ignored by every runtime and by the lines. Rust instantiates before it checks the sources; the line claims only the refusal, not which check reports it."
          "Line 2 is the first two quoted sentences. It constrains only a call that returns a result, as the first sentence's trigger says, and claims nothing about a call that is refused for another reason. The second sentence is its contrapositive: a report requires the instance under sut and the synthetic net, so a call whose instantiation or build fails fails too (mod051_fails_of_build). The runtimes instantiate under sut (harness.rs:369, SubnetDef.java:288, subnet-def.ts:266), bind every port to its harness place and compose once on a new builder, then build (harness.rs:430-432, SubnetDef.java:347-349, subnet-def.ts:340-342); channels are not bound and flow through as renamed transitions (MOD-021). The enclosing net's name (verify_<definition>) is not modelled, as no net name is (MOD-050). The harness place names are what a property, a sink place or a carrier place set through the hook names, so they are part of the contract; the subnet's own places are named sut/<place> by MOD-010. A wrong synthetic net that adds a generator transition feeding the input place is killed (MOD_051_forbids_generator). The prose sentence that an implementation MAY wrap the subnet in such a net and invoke the standard verifier per MOD-050 is reworded under D20 to say that it does, as every runtime does; MOD-050 then makes the verifier see the synthetic net as a hand-written net."
          "Line 3 is the fourth quoted sentence and the bindActions paragraph's 'The [CORE-043] check in `verify` applies to the bound definition as to any other.' Every runtime runs the check on the synthetic net before any property (harness.rs:436, SubnetDef.java:351-353, subnet-def.ts:344-346), so it fails also with no property. C is CORE-043's compile check, which names the first output-declaring transition that carries passthrough (CORE_043 line 1); the line asks that the message names it (MsgNames), not its bytes. CORE-043 line 3 already binds each per-property SMT entry point; this line binds verify's own check, which also runs when there is no property. A verify without the check is killed (MOD_051_forbids_noCore043)."
          "Line 4 is the fifth quoted sentence, item 4 (the mode is supplied in the options of verify or defaulted, not carried by the harness: Java's VerificationHarness record holds the parameters, the generators and the properties only, java/src/main/java/org/libpetri/verification/VerificationHarness.java:60-64), the option bullet 'a configure hook, called once per property with the per-property verifier after the implementation's own setup (property, environment places, environment mode) and with the synthetic net, returning the verifier to run', and the hook's override semantics (run_per_property in harness.rs, the per-property loop of SubnetDef.verify in SubnetDef.java and in subnet-def.ts). The setup is a value (VerifySetup) and the hook a function on it that also receives the synthetic net; a hook that returns a verifier for another net is outside the model. The default options and the empty initial marking are the verifier's defaults (SmtVerifier::for_net in rust/libpetri-verification/src/smt_verifier.rs, java/src/main/java/org/libpetri/smt/SmtVerifier.java:126, typescript/src/verification/smt-verifier.ts:141); the verifier reads no deadline tolerance, so the synthetic net is handed with tolerance 0. D is VER-006's environment-aware decider (EnvDecider): the standard verifier with the mode and the registered environment places, whose verdict lines then apply to every entry. Wrong setups are killed: no environment place registered (MOD_051_forbids_noEnvs, under which the forwarder proves PlaceBound(harness_out_out, 0)), the output ports registered too (MOD_051_forbids_outputsAsEnv, under which Bounded(0) refuses every subnet that writes its output port) and the setup applied after the hook, so that the hook cannot change the mode (MOD_051_forbids_hookFirst)."
          "A Rust build without the z3 feature has no standard verifier: every entry is Unknown with route Unavailable and the configure hook is not called (rust/libpetri-verification/src/harness.rs:478-500; the feature is off by default, rust/libpetri-verification/Cargo.toml). That build is line 4 with D the constant Unknown decider, and AC6 holds only of a build with the solver (VER-013)."
          "Line 4 claims no order. Rust keeps the harness's property order and its duplicates; Java's VerificationHarness record copies the properties with Set.copyOf (java/src/main/java/org/libpetri/verification/VerificationHarness.java:73), which keeps no order although its comment says it does, and Java and TypeScript return a map keyed by property. The environment places are a permutation of the harness places of the input and in-out ports, in the order the interface yields its ports, one list for the whole call. Several entries for one property are allowed, as the quoted 'each entry for a property' says. Every runtime sets the environment places and the selected mode on every per-property call, also for a subnet without an input or in-out port: Rust (harness.rs:465-468), Java (SubnetDef.java:368-371) and TypeScript (subnet-def.ts:359-361), and Python rides on Rust. So a hook that registers an environment place itself runs under the selected mode. The line keeps the spec's 'the selected environment mode' and kills a verify that hands over the selected mode only when the harness has an environment place and leaves the verifier on its default mode AlwaysAvailable otherwise (MOD_051_forbids_modeOnlyWithEnvs, the behaviour RD-29 recorded)."
          "Line 5 is the sixth quoted sentence and 'verify therefore SHOULD default to AlwaysAvailable, under which a Proven holds for every environment, and SHOULD let the caller pass a mode instead' (harness.rs:217-221 and :336-338, SubnetDef.java:213-215, subnet-def.ts:261, verification.rs:1062-1066). AC4 (the mode is selectable per verification and defaults to one that models injection, so a subnet with an input port is not refused a Proven by default) is lines 4 and 5 with VER-006: by default every entry is D under AlwaysAvailable with the input places registered (mod051_default), and only Ignore refuses every Proven (VER_006_verdict line 1). On the forwarder the reference proves TerminatesAtSink(harness_out_out) by default and answers Unknown for PlaceBound(harness_out_out, 0) under Ignore (MOD_051_nonvacuous). A verify whose default is Ignore is killed (MOD_051_forbids_defaultIgnore)."
          "The paragraph on what a verdict is worth under each mode (Ignore refuses every Proven, a Violated still comes back; Bounded(k) caps the resident tokens; Arrivals(k) bounds the total; Arrivals(k, k) delivers exactly k) restates VER-006 on the synthetic net and is reworded under ruling D49 (a), VB2: a Violated under Ignore is a counterexample with injection for a reachability-safety property only, and a rest of the subnet while the environment stays silent for a quiescence property (VER_006_verdict line 3, VER_006_frozen_in_injected). AC5 (a forwarding subnet proves PlaceBound of its output at k under Arrivals(k) and violates it under Bounded(k)) is line 4 handing D the mode Arrivals(0, k) or Bounded(k) on the synthetic net, which for the forwarder is VER-006's env IN → T → OUT renamed (mod051_fwd_synth); the verdicts are VER-006's AC9 and are delegated to it, not computed here, since the reference decider steps aside under Arrivals. The Proven under Arrivals(k) is VER_006_arrivals line 1 (OUT holds at most the arrivals so far; a closure without the optional source is killed by VER_006_arrivals_forbids_noOpt). The Violated under Bounded(k) is a completeness claim, which VER-006 leaves to the runtimes' env IN → T → OUT tests: its lines, the Bounded(k) reachable set of VER_006 line 3 among them, rule out a wrong Proven only."
          "AC1 (a result of the same shape as VER-003's) is the type of the entries, D's Result. AC2 (no enclosing net needed) is the type of SV, which takes a definition. AC6 (the hook, or Python's keywords, reaches every per-property verifier, and a setting made there is visible) is line 4: every entry runs the setup the hook returns. Python's keywords are such a hook (the with_configure closure of py_verify_subnet, verification.rs:1081-1134). That a total budget too small to finish gives its exhaustion reason, and a sink place named there changes a quiescence verdict, is VER-013's and VER-014's over that setup; the setup's Options carry neither field, so those halves are tested, not stated here (open item). AC7 (ν options reach the verifier and change the model) and the paragraph 'ν subnets need the ν options' rest on NU-051 and NU-052; the setup here carries no ν option (open item). The Python keyword list, the unknown-name behaviour of sink and carrier places and the implementation notes are kind N. Cancellation through the thread interrupt is VER-013's."
          "That verify returns a report whenever nothing is refused is the existence half of the requirement ('A subnet definition SHOULD support a local verification operation'), the coverage condition Mod051Covers, not a line: a verify that refuses every call meets lines 1 to 5 (mod051_rejectAll_meets) and is killed by the coverage condition (mod051_rejectAll_not_covers), which every runtime and the reference meet (mod051_ref_covers)."
  signoff "2026-11-13 c442a9bd4be9999a ai"
  statement : ∀ {A : Type}, InstFn String A → ScriptFn String A →
      (BuiltNet String A → Option String) → EnvDecider String → SubnetVerifyFn A → Prop :=
    fun Inst BS C D SV =>
      (∀ S h o, sourcesOk S h = false → ∃ msg, SV S h o = .error msg) ∧
      (∀ S h o r, SV S h o = .ok r →
        ∃ I, Inst S "sut" = .ok I ∧ BS (synthScript S I) = .ok r.synth) ∧
      (∀ S h o I c n, sourcesOk S h = true → Inst S "sut" = .ok I →
        BS (synthScript S I) = .ok c → C c.toBuiltNet = some n →
        ∃ msg, SV S h o = .error msg ∧ MsgNames msg n) ∧
      (∀ S h o r, SV S h (some o) = .ok r →
        ∃ envs, envs.Perm (harnessEnvs S) ∧
          (∀ e ∈ r.results, e.1 ∈ h.props ∧ e.2 = verifyOne D o r.synth envs e.1) ∧
          ∀ φ ∈ h.props, ∃ e ∈ r.results, e.1 = φ) ∧
      (∀ S h, SV S h none = SV S h (some defaultVerifyOpts))

/- The pinned readable form of MOD-051: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_051 : {A : Type} →
  InstFn String A →
    ScriptFn String A → (BuiltNet String A → Option String) → EnvDecider String → SubnetVerifyFn A → Prop :=
fun {A} Inst BS C D SV =>
  (∀ (S : SubnetDef String A) (h : SubnetHarness) (o : Option (SubnetVerifyOpts A)),
      sourcesOk S h = false → ∃ msg, SV S h o = Except.error msg) ∧
    (∀ (S : SubnetDef String A) (h : SubnetHarness) (o : Option (SubnetVerifyOpts A)) (r : SubnetReport A),
        SV S h o = Except.ok r → ∃ I, Inst S "sut" = Except.ok I ∧ BS (synthScript S I) = Except.ok r.synth) ∧
      (∀ (S : SubnetDef String A) (h : SubnetHarness) (o : Option (SubnetVerifyOpts A)) (I : Instance String A)
          (c : ComposedNet String A) (n : String),
          sourcesOk S h = true →
            Inst S "sut" = Except.ok I →
              BS (synthScript S I) = Except.ok c →
                C c.toBuiltNet = some n → ∃ msg, SV S h o = Except.error msg ∧ MsgNames msg n) ∧
        (∀ (S : SubnetDef String A) (h : SubnetHarness) (o : SubnetVerifyOpts A) (r : SubnetReport A),
            SV S h (some o) = Except.ok r →
              ∃ envs,
                envs.Perm (harnessEnvs S) ∧
                  (∀ e ∈ r.results, e.1 ∈ h.props ∧ e.2 = verifyOne D o r.synth envs e.1) ∧
                    ∀ φ ∈ h.props, ∃ e ∈ r.results, e.1 = φ) ∧
          ∀ (S : SubnetDef String A) (h : SubnetHarness), SV S h none = SV S h (some defaultVerifyOpts)
-/
#guard_msgs in #print MOD_051

/-! ### The reference -/

/-- ✓ **The reference `verify` meets the five lines, for every choice of its parts.** Example:
on the forwarder with a token source for `in`, `verify` instantiates it under `sut`, binds `in`
to `harness_in_in` and `out` to `harness_out_out`, checks [CORE-043], and runs the verifier
once per property with `harness_in_in` registered under `AlwaysAvailable`. -/
@[evidence holds MOD_051]
theorem MOD_051_reference {A : Type} (Inst : InstFn String A) (BS : ScriptFn String A)
    (C : BuiltNet String A → Option String) (D : EnvDecider String) :
    MOD_051 Inst BS C D (refVerifySubnet Inst BS C D) := by
  refine ⟨?_, ?_, ?_, ?_, fun _ _ => rfl⟩
  · intro S h o hs
    exact ⟨missingSourceMsg, by simp [refVerifySubnet, hs]⟩
  · intro S h o r hr
    simp only [refVerifySubnet] at hr
    split at hr
    · split at hr
      · cases hr
      · rename_i I hI
        split at hr
        · cases hr
        · rename_i c hc
          split at hr
          · cases hr
          · cases hr
            exact ⟨I, hI, hc⟩
    · cases hr
  · intro S h o I c n hs hI hc hC
    exact ⟨core043VerifyMsg n, by simp [refVerifySubnet, hs, hI, hc, hC],
      msgNames_mid _ _ _⟩
  · intro S h o r hr
    simp only [refVerifySubnet, Option.getD_some] at hr
    split at hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
        · rename_i c _
          split at hr
          · cases hr
          · cases hr
            refine ⟨harnessEnvs S, List.Perm.refl _, ?_, ?_⟩
            · intro e he
              obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 he
              exact ⟨hφ, rfl⟩
            · intro φ hφ
              exact ⟨(φ, _), List.mem_map.2 ⟨φ, hφ, rfl⟩, rfl⟩
    · cases hr

/-! ### Consequences for every model of the block -/

section Consequences

variable {A : Type} {Inst : InstFn String A} {BS : ScriptFn String A}
  {C : BuiltNet String A → Option String} {D : EnvDecider String} {SV : SubnetVerifyFn A}

/-- **One entry, in every model.** An entry of a report is the decider's result on the
synthetic net the script builds from the `sut` instance, for one list of environment places
that is a permutation of the harness places of the input and in-out ports. -/
theorem mod051_entry (hM : MOD_051 Inst BS C D SV) {S : SubnetDef String A} {h : SubnetHarness}
    {o : SubnetVerifyOpts A} {r : SubnetReport A} (hr : SV S h (some o) = .ok r)
    {e : VerProp String × Result String} (he : e ∈ r.results) :
    ∃ I envs, Inst S "sut" = .ok I ∧ BS (synthScript S I) = .ok r.synth ∧
      envs.Perm (harnessEnvs S) ∧ e.1 ∈ h.props ∧ e.2 = verifyOne D o r.synth envs e.1 := by
  obtain ⟨I, hI, hB⟩ := hM.2.1 S h (some o) r hr
  obtain ⟨envs, hp, hall, -⟩ := hM.2.2.2.1 S h o r hr
  exact ⟨I, envs, hI, hB, hp, (hall e he).1, (hall e he).2⟩

/-- **AC4: by default, injection is modelled.** In every model, an entry of a call without
options is the decider under `AlwaysAvailable` with the harness's input places registered, the
default options and the empty marking: a subnet with an input port is verified as an open net
whose environment may inject at any time, never under `Ignore`. -/
@[evidence cites "MOD-051" "AC4: the environment-analysis mode defaults to one that models injection, so a subnet with an input port is not refused a Proven by default: in every model of the MOD-051 block, an entry of a call without options is the verifier under AlwaysAvailable with the harness places of the input ports registered"]
theorem mod051_default (hM : MOD_051 Inst BS C D SV) {S : SubnetDef String A}
    {h : SubnetHarness} {r : SubnetReport A} (hr : SV S h none = .ok r)
    {e : VerProp String × Result String} (he : e ∈ r.results) :
    ∃ envs, envs.Perm (harnessEnvs S) ∧
      e.2 = D .always envs {} (r.synth.toTimed 0) e.1 emptyNM := by
  rw [hM.2.2.2.2 S h] at hr
  obtain ⟨-, envs, -, -, hp, -, h2⟩ := mod051_entry hM hr he
  exact ⟨envs, hp, h2⟩

/-- **A call whose synthetic net does not build fails, in every model.** If instantiating the
definition under `sut` fails, or the instance exists but the one-call synthetic script does not
build, `verify` fails: a report would need both. Example: a definition whose instance cannot be
made under `sut` gets an error from `verify`, never a report with some other net. -/
@[evidence cites "MOD-051" "If instantiating the subnet under the prefix sut fails or building the synthetic net fails, then verify shall fail: in every model of the MOD-051 block a report needs the instance and the synthetic net, so a call without them fails"]
theorem mod051_fails_of_build (hM : MOD_051 Inst BS C D SV) (S : SubnetDef String A)
    (h : SubnetHarness) (o : Option (SubnetVerifyOpts A))
    (hfail : (∃ m, Inst S "sut" = .error m) ∨
      (∃ I m, Inst S "sut" = .ok I ∧ BS (synthScript S I) = .error m)) :
    ∃ msg, SV S h o = .error msg := by
  cases hsv : SV S h o with
  | error msg => exact ⟨msg, rfl⟩
  | ok r =>
    obtain ⟨I, hI, hB⟩ := hM.2.1 S h o r hsv
    rcases hfail with ⟨m, hm⟩ | ⟨I', m, hI', hm⟩
    · rw [hI] at hm; cases hm
    · rw [hI] at hI'; cases hI'; rw [hB] at hm; cases hm

end Consequences

/-! ### Coverage: `verify` answers when nothing is refused -/

/-- **The coverage condition of MOD-051**: when every input and in-out port has a token
source, the instance under `sut` exists, the synthetic script builds and the [CORE-043] check
passes, `verify` returns a report. -/
def Mod051Covers {A : Type} (Inst : InstFn String A) (BS : ScriptFn String A)
    (C : BuiltNet String A → Option String) (SV : SubnetVerifyFn A) : Prop :=
  ∀ S h o I c, sourcesOk S h = true → Inst S "sut" = .ok I → BS (synthScript S I) = .ok c →
    C c.toBuiltNet = none → ∃ r, SV S h o = .ok r

/-- The reference `verify` returns a report whenever nothing is refused: on the forwarder with a
token source for `in`, the synthetic net builds, passes [CORE-043] and gets one entry per
property. -/
@[evidence cites "MOD-051" "A subnet definition SHOULD support a local verification operation `verify(harness)` that proves properties of the subnet **in isolation**, without first composing it into an enclosing net: the reference verify returns a report whenever every input and in-out port has a token source, the instance and the synthetic net build and the CORE-043 check passes"]
theorem mod051_ref_covers {A : Type} (Inst : InstFn String A) (BS : ScriptFn String A)
    (C : BuiltNet String A → Option String) (D : EnvDecider String) :
    Mod051Covers Inst BS C (refVerifySubnet Inst BS C D) := by
  intro S h o I c hs hI hc hC
  exact ⟨⟨c, h.props.map fun φ => (φ, verifyOne D (o.getD defaultVerifyOpts) c (harnessEnvs S) φ)⟩,
    by simp [refVerifySubnet, hs, hI, hc, hC]⟩

/-- A `verify` that refuses every call: it fails where the reference fails, with the
reference's message, and fails with `refused` where the reference would return a report. -/
def mod051RejectAll {A : Type} (Inst : InstFn String A) (BS : ScriptFn String A)
    (C : BuiltNet String A → Option String) (D : EnvDecider String) : SubnetVerifyFn A :=
  fun S h o =>
    match refVerifySubnet Inst BS C D S h o with
    | .ok _ => .error "refused"
    | .error m => .error m

/-- A `verify` that refuses every call meets the five lines: the lines rule out wrong answers,
not missing ones. Example: refusing the forwarder with every token source supplied breaks no
line. -/
theorem mod051_rejectAll_meets {A : Type} (Inst : InstFn String A) (BS : ScriptFn String A)
    (C : BuiltNet String A → Option String) (D : EnvDecider String) :
    MOD_051 Inst BS C D (mod051RejectAll Inst BS C D) := by
  have hR := MOD_051_reference Inst BS C D
  have hok : ∀ S h o r, mod051RejectAll Inst BS C D S h o ≠ .ok r := by
    intro S h o r hr
    simp only [mod051RejectAll] at hr
    split at hr <;> cases hr
  refine ⟨fun S h o hs => ?_, fun S h o r hr => absurd hr (hok S h o r),
    fun S h o I c n hs hI hc hC => ?_, fun S h o r hr => absurd hr (hok S h o r),
    fun S h => ?_⟩
  · obtain ⟨msg, hm⟩ := hR.1 S h o hs
    exact ⟨msg, by simp [mod051RejectAll, hm]⟩
  · obtain ⟨msg, hm, hn⟩ := hR.2.2.1 S h o I c n hs hI hc hC
    exact ⟨msg, by simp [mod051RejectAll, hm], hn⟩
  · simp only [mod051RejectAll, hR.2.2.2.2 S h]

/-! ## The worked example: the forwarding subnet -/

section Example

/-- The forwarding subnet `fwd`: input port `in` over `IN`, transition `work` from `IN` to
`OUT` with a hand-written action, output port `out` over `OUT`. -/
def mod051Fwd : SubnetDef String Unit :=
  { name := "fwd", places := ["IN", "OUT"],
    defs := [{ core := ⟨"work", [⟨"IN", .one⟩], [], [], []⟩, out := some (.place "OUT"),
               timing := .immediate, priority := 0, action := .other () }],
    ports := [⟨"in", .input, "IN"⟩, ⟨"out", .output, "OUT"⟩], chans := [] }

/-- The same subnet with `work` left on the builder default, passthrough ([CORE-043]). -/
def mod051FwdPT : SubnetDef String Unit :=
  { mod051Fwd with
    defs := [{ core := ⟨"work", [⟨"IN", .one⟩], [], [], []⟩, out := some (.place "OUT"),
               timing := .immediate, priority := 0, action := .passthrough }] }

/-- `verify` at the reference parts: instantiation `refInst`, the reference build script, the
[CORE-043] compile check `refCompile` and the [VER-006] decider `refEnvVerify`. -/
def mod051RefEx : SubnetVerifyFn Unit :=
  refVerifySubnet (refInst strNaming) buildExScript refCompile refEnvVerify

/-- A harness with a token source for `in` and the given properties. -/
def mod051H (ps : List (VerProp String)) : SubnetHarness := ⟨["in"], ps⟩

/-- The verdicts of a call, `none` when it fails. -/
def mod051Verdicts {A : Type} (x : Except String (SubnetReport A)) : Option (List Verifier.Verdict) :=
  x.toOption.map fun r => r.results.map (·.2.verdict)

/-- The synthetic net of the forwarder, if it builds. -/
def mod051FwdSynth : Option (ComposedNet String Unit) :=
  (refInst strNaming mod051Fwd "sut").toOption.bind fun I =>
    (buildExScript (synthScript mod051Fwd I)).toOption

set_option maxRecDepth 20000 in
/-- **The forwarder's synthetic net is `harness_in_in → sut/work → harness_out_out`**: the two
harness places, and the one transition `sut/work` from the input harness place to the output
harness place, VER-006's `env IN → T → OUT` renamed. -/
@[evidence cites "MOD-051" "AC5: a subnet that forwards each input token to an output port: its synthetic net is the environment net env IN → T → OUT of VER-006 AC9, with IN the harness place of its input port and OUT the harness place of its output port"]
theorem mod051_fwd_synth :
    mod051FwdSynth.map (fun c => (c.places, c.trans.map fun d =>
      (d.core.name, d.core.inputs.map (·.place), d.out.map Spec.outPlaces))) =
      some (["harness_in_in", "harness_out_out"],
        [("sut/work", ["harness_in_in"], some ["harness_out_out"])]) := by
  decide

set_option maxRecDepth 20000 in
/-- ✓ **The reference on the forwarder.** By default (`AlwaysAvailable`, `harness_in_in`
registered) `TerminatesAtSink({harness_out_out})` is `Proven`: `sut/work` takes its only token
from the environment, so no marking can rest. `PlaceBound(harness_out_out, 0)` is `Unknown`
there: the environment may push tokens through, and the reference decides only the vacuous
quiescence properties under injection. Under `Ignore` the same two give
`Violated` (the empty marking rests while the environment stays silent) and `Unknown` (the
dead-marking proof is refused). A harness without a source for `in` is refused, and so is the
subnet whose `work` keeps passthrough, naming `sut/work`. -/
@[evidence nonvacuous MOD_051]
theorem MOD_051_nonvacuous :
    mod051Verdicts (refVerifySubnet (refInst strNaming) buildExScript refCompile refEnvVerify mod051Fwd
        (mod051H [.terminatesAtSink ["harness_out_out"], .placeBound "harness_out_out" 0]) none) =
      some [.proven "vacuous", .unknown injectionAsideReason] ∧
    mod051Verdicts (refVerifySubnet (refInst strNaming) buildExScript refCompile refEnvVerify mod051Fwd
        (mod051H [.terminatesAtSink ["harness_out_out"], .placeBound "harness_out_out" 0])
        (some ⟨.ignore, fun _ s => s⟩)) =
      some [.violated, .unknown ignoreReason] ∧
    mod051Verdicts (refVerifySubnet (refInst strNaming) buildExScript refCompile refEnvVerify mod051Fwd ⟨[], [.placeBound "harness_out_out" 0]⟩ none) = none ∧
    (refVerifySubnet (refInst strNaming) buildExScript refCompile refEnvVerify mod051FwdPT (mod051H []) none).toOption.isNone = true ∧
    (match refVerifySubnet (refInst strNaming) buildExScript refCompile refEnvVerify mod051FwdPT (mod051H []) none with
      | .error m => m
      | .ok _ => "") = core043VerifyMsg "sut/work" := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The refusal of a call that does not fail. -/
theorem mod051_not_error {A : Type} {x : Except String (SubnetReport A)}
    (h : x.toOption.isSome = true) (msg : String) : x ≠ .error msg := by
  rintro rfl
  simp [Except.toOption] at h

/-- An `Except` whose value maps to `b` holds a value that maps to `b`. -/
theorem mod051_ok_of {α β : Type} {x : Except String α} {f : α → β} {b : β}
    (h : x.toOption.map f = some b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error m => simp [Except.toOption] at h
  | ok a => exact ⟨a, rfl, by simpa [Except.toOption] using h⟩

/-- The verdict the decider `D` gives the property `φ` on the forwarder's synthetic net under the
options `o`, with `harness_in_in` registered. -/
def mod051ExVerdict (D : EnvDecider String) (o : SubnetVerifyOpts Unit) (φ : VerProp String) :
    Option Verifier.Verdict :=
  mod051FwdSynth.map fun c => (verifyOne D o c ["harness_in_in"] φ).verdict

/-- **In every model at the reference parts, the forwarder's verdict is the decider's.** A call
with one property `φ` that returns a report has, for each entry, the verdict `D` gives `φ` on
the synthetic net with `harness_in_in` registered. -/
theorem mod051_ex_verdict {D : EnvDecider String} {SV : SubnetVerifyFn Unit}
    (hM : MOD_051 (refInst strNaming) buildExScript refCompile D SV) {φ : VerProp String}
    {o : SubnetVerifyOpts Unit} {r : SubnetReport Unit}
    (hr : SV mod051Fwd (mod051H [φ]) (some o) = .ok r)
    {e : VerProp String × Result String} (he : e ∈ r.results) :
    mod051ExVerdict D o φ = some e.2.verdict := by
  obtain ⟨I, envs, hI, hB, hp, h1, h2⟩ := mod051_entry hM hr he
  have hh : harnessEnvs mod051Fwd = ["harness_in_in"] := by decide
  rw [hh] at hp
  have henvs : envs = ["harness_in_in"] := List.perm_singleton.1 hp
  have hφ : e.1 = φ := by simpa [mod051H] using h1
  simp only [mod051ExVerdict, mod051FwdSynth, hI, hB, Except.toOption, Option.bind_some,
    Option.map_some]
  rw [h2, henvs, hφ]

/-- The verdict of the first entry of a call that returns one entry. -/
theorem mod051_first {A : Type} {x : Except String (SubnetReport A)} {v : Verifier.Verdict}
    (h : mod051Verdicts x = some [v]) :
    ∃ r e, x = .ok r ∧ e ∈ r.results ∧ e.2.verdict = v := by
  obtain ⟨r, hr, hv⟩ := mod051_ok_of h
  match hres : r.results, hv with
  | [e], _ => exact ⟨r, e, hr, by simp [hres], by simp_all⟩

end Example

/-! ### Wrong `verify`s, one per line -/

section Mutants

variable {A : Type}

/-- The knobs of a `verify` that differs from the reference in one step. -/
structure Mod051Knobs (A : Type) where
  /-- The registered environment places. -/
  envsOf : SubnetDef String A → List String
  /-- Calls added to the synthetic script. -/
  extra : List (Op String A)
  /-- Whether the token sources are checked. -/
  checkSources : Bool
  /-- Whether the [CORE-043] check runs. -/
  check043 : Bool
  /-- One per-property verification. -/
  run : EnvDecider String → SubnetVerifyOpts A → ComposedNet String A → List String →
    VerProp String → Result String
  /-- The options of a call without options. -/
  dflt : SubnetVerifyOpts A

/-- The reference's knobs. -/
def mod051RefKnobs : Mod051Knobs A :=
  ⟨harnessEnvs, [], true, true, verifyOne, defaultVerifyOpts⟩

/-- `verify` with the given knobs (the reference with `mod051RefKnobs`). -/
def mod051Variant (k : Mod051Knobs A) (Inst : InstFn String A) (BS : ScriptFn String A)
    (C : BuiltNet String A → Option String) (D : EnvDecider String) : SubnetVerifyFn A :=
  fun S h o? =>
    let o := o?.getD k.dflt
    if !k.checkSources || sourcesOk S h then
      match Inst S "sut" with
      | .error m => .error m
      | .ok I =>
        match BS (synthScript S I ++ k.extra) with
        | .error m => .error m
        | .ok c =>
          match (if k.check043 then C c.toBuiltNet else none) with
          | some n => .error (core043VerifyMsg n)
          | none => .ok ⟨c, h.props.map fun φ => (φ, k.run D o c (k.envsOf S) φ)⟩
    else .error missingSourceMsg

/-- A wrong `verify` at the reference parts. -/
def mod051Wrong (k : Mod051Knobs Unit) : SubnetVerifyFn Unit :=
  mod051Variant k (refInst strNaming) buildExScript refCompile refEnvVerify

/-- ✗ **A missing token source is refused** (line 1). Example: the forwarder with no source for
its input port `in`; a `verify` that skips the check verifies it anyway. -/
@[evidence forbids MOD_051]
theorem MOD_051_forbids_noSourceCheck :
    ¬ MOD_051 (refInst strNaming) buildExScript refCompile refEnvVerify
      (mod051Wrong { mod051RefKnobs with checkSources := false }) := by
  intro hM
  obtain ⟨msg, hm⟩ := hM.1 mod051Fwd ⟨[], []⟩ none (by decide)
  exact mod051_not_error (by decide) msg hm

/-- The generator transition of the wrong synthetic net: no input, one token into
`harness_in_in`. -/
def mod051Gen : CDef String Unit :=
  { core := ⟨"harness_gen_in", [], [], [], []⟩, out := some (.place "harness_in_in"),
    timing := .immediate, priority := 0, action := .other () }

set_option maxRecDepth 20000 in
/-- ✗ **The synthetic net declares nothing else** (line 2). Example: a `verify` that also adds a
generator transition feeding `harness_in_in` hands the verifier a net with two transitions,
not the one the script builds; the generator would fix the input behaviour that the
environment mode is meant to set. -/
@[evidence forbids MOD_051]
theorem MOD_051_forbids_generator :
    ¬ MOD_051 (refInst strNaming) buildExScript refCompile refEnvVerify
      (mod051Wrong { mod051RefKnobs with extra := [.trans mod051Gen] }) := by
  intro hM
  obtain ⟨r, hr, hlen⟩ := mod051_ok_of (f := fun r => r.synth.trans.length) (b := 2)
    (x := mod051Wrong { mod051RefKnobs with extra := [.trans mod051Gen] } mod051Fwd
      (mod051H []) none) (by decide)
  obtain ⟨I, hI, hB⟩ := hM.2.1 _ _ _ r hr
  have h1 : mod051FwdSynth.map (fun c => c.trans.length) = some 1 := by decide
  simp only [mod051FwdSynth, hI, hB, Except.toOption, Option.bind_some, Option.map_some,
    Option.some.injEq] at h1
  omega

set_option maxRecDepth 20000 in
/-- ✗ **The [CORE-043] check runs in `verify`** (line 3). Example: the forwarder whose `work`
keeps passthrough although it declares an output; a `verify` without the check returns a report
for it instead of failing on `sut/work`. -/
@[evidence forbids MOD_051]
theorem MOD_051_forbids_noCore043 :
    ¬ MOD_051 (refInst strNaming) buildExScript refCompile refEnvVerify
      (mod051Wrong { mod051RefKnobs with check043 := false }) := by
  intro hM
  obtain ⟨I, hI, hc'⟩ := mod051_ok_of (x := refInst strNaming mod051FwdPT "sut")
    (f := fun I => (buildExScript (synthScript mod051FwdPT I)).toOption.map
      (fun c => refCompile c.toBuiltNet)) (b := some (some "sut/work")) (by decide)
  obtain ⟨c, hc, hC⟩ := mod051_ok_of hc'
  obtain ⟨msg, hm, -⟩ := hM.2.2.1 mod051FwdPT (mod051H []) none I c "sut/work"
    (by decide) hI hc hC
  exact mod051_not_error (by decide) msg hm

set_option maxRecDepth 20000 in
/-- ✗ **The input places are registered** (line 4). Example: a `verify` that registers no
environment place verifies the forwarder as a closed net from the empty marking, where nothing
fires, and proves `PlaceBound(harness_out_out, 0)`; with `harness_in_in` registered under
`AlwaysAvailable` the environment can push tokens through, and the verifier does not prove it. -/
@[evidence forbids MOD_051]
theorem MOD_051_forbids_noEnvs :
    ¬ MOD_051 (refInst strNaming) buildExScript refCompile refEnvVerify
      (mod051Wrong { mod051RefKnobs with envsOf := fun _ => [] }) := by
  intro hM
  obtain ⟨r, e, hr, he, hv⟩ := mod051_first (x := mod051Wrong
    { mod051RefKnobs with envsOf := fun _ => [] } mod051Fwd
    (mod051H [.placeBound "harness_out_out" 0]) (some defaultVerifyOpts))
    (v := .proven "enumeration") (by decide)
  have h := mod051_ex_verdict hM hr he
  rw [hv] at h
  exact absurd h (by decide)

set_option maxRecDepth 20000 in
/-- ✗ **Only the input and in-out ports are registered** (line 4). Example: a `verify` that
also registers `harness_out_out` makes `sut/work` deposit into an environment place, so under
`Bounded(0)` the premise check fails and every property of the forwarder is refused with the
premise reason; with only `harness_in_in` registered the premises hold. -/
@[evidence forbids MOD_051]
theorem MOD_051_forbids_outputsAsEnv :
    ¬ MOD_051 (refInst strNaming) buildExScript refCompile refEnvVerify
      (mod051Wrong { mod051RefKnobs with envsOf := fun S => S.ports.map harnessPlace }) := by
  intro hM
  obtain ⟨r, e, hr, he, hv⟩ := mod051_first (x := mod051Wrong
    { mod051RefKnobs with envsOf := fun S => S.ports.map harnessPlace } mod051Fwd
    (mod051H [.terminatesAtSink ["harness_out_out"]]) (some ⟨.bounded 0, fun _ s => s⟩))
    (v := .unknown premiseReason) (by decide)
  have h := mod051_ex_verdict hM hr he
  rw [hv] at h
  exact absurd h (by decide)

/-- One per-property verification with the setup applied after the hook: the hook's mode is
overwritten. -/
def mod051HookFirst (D : EnvDecider String) (o : SubnetVerifyOpts Unit)
    (c : ComposedNet String Unit) (envs : List String) (φ : VerProp String) : Result String :=
  let s := o.hook c ⟨φ, envs, o.mode, {}, emptyNM⟩
  D o.mode envs s.opts (c.toTimed 0) φ s.m0

/-- A hook that switches the mode to `Ignore`. -/
def mod051ToIgnore : SubnetVerifyOpts Unit := ⟨.always, fun _ s => { s with mode := .ignore }⟩

set_option maxRecDepth 20000 in
/-- ✗ **What the hook sets overrides the setup** (line 4). Example: a hook that switches the mode
to `Ignore`; a `verify` that applies its own setup after the hook keeps `AlwaysAvailable` and
proves `TerminatesAtSink({harness_out_out})` vacuously, where the verifier the hook returned
finds the empty marking at rest and answers `Violated`. -/
@[evidence forbids MOD_051]
theorem MOD_051_forbids_hookFirst :
    ¬ MOD_051 (refInst strNaming) buildExScript refCompile refEnvVerify
      (mod051Wrong { mod051RefKnobs with run := mod051HookFirst }) := by
  intro hM
  obtain ⟨r, e, hr, he, hv⟩ := mod051_first (x := mod051Wrong
    { mod051RefKnobs with run := mod051HookFirst } mod051Fwd
    (mod051H [.terminatesAtSink ["harness_out_out"]]) (some mod051ToIgnore))
    (v := .proven "vacuous") (by decide)
  have h := mod051_ex_verdict hM hr he
  rw [hv] at h
  exact absurd h (by decide)

set_option maxRecDepth 20000 in
/-- ✗ **The default is `AlwaysAvailable`** (line 5). Example: a `verify` whose call without
options runs under `Ignore` answers `Violated` for `TerminatesAtSink({harness_out_out})` on the
forwarder (the empty marking rests while the environment is silent), where the call with the
default options proves it: the two calls must agree. -/
@[evidence forbids MOD_051]
theorem MOD_051_forbids_defaultIgnore :
    ¬ MOD_051 (refInst strNaming) buildExScript refCompile refEnvVerify
      (mod051Wrong { mod051RefKnobs with dflt := ⟨.ignore, fun _ s => s⟩ }) := by
  intro hM
  have h := congrArg mod051Verdicts (hM.2.2.2.2 mod051Fwd
    (mod051H [.terminatesAtSink ["harness_out_out"]]))
  have h1 : mod051Verdicts (mod051Wrong { mod051RefKnobs with dflt := ⟨.ignore, fun _ s => s⟩ }
      mod051Fwd (mod051H [.terminatesAtSink ["harness_out_out"]]) none) = some [.violated] := by
    decide
  have h2 : mod051Verdicts (mod051Wrong { mod051RefKnobs with dflt := ⟨.ignore, fun _ s => s⟩ }
      mod051Fwd (mod051H [.terminatesAtSink ["harness_out_out"]]) (some defaultVerifyOpts)) =
      some [.proven "vacuous"] := by
    decide
  rw [h1, h2] at h
  exact absurd h (by decide)

/-- A wrong per-property verification that hands over the selected mode only when there is a
harness environment place, and the verifier default `AlwaysAvailable` otherwise (the behaviour
RD-29 recorded). -/
def mod051ModeOnlyWithEnvs (D : EnvDecider String) (o : SubnetVerifyOpts Unit)
    (c : ComposedNet String Unit) (envs : List String) (φ : VerProp String) : Result String :=
  verifyOne D (if envs.isEmpty then { o with mode := .always } else o) c envs φ

/-- The forwarder without its input port: `IN` is an internal place, `out` the only port. -/
def mod051Closed : SubnetDef String Unit := { mod051Fwd with ports := [⟨"out", .output, "OUT"⟩] }

/-- `Ignore` selected, and a hook that registers the internal place `sut/IN` as an environment
place. -/
def mod051IgnoreOwnEnv : SubnetVerifyOpts Unit :=
  ⟨.ignore, fun _ s => { s with envs := ["sut/IN"] }⟩

set_option maxRecDepth 20000 in
/-- ✗ **The selected mode is set also without a harness environment place** (line 4; the wrong
shape is the behaviour RD-29 recorded). Example: the forwarder without its input port, verified under `Ignore` with a hook
that registers `sut/IN` as an environment place. Under `Ignore` the empty marking rests while the
environment stays silent, so `TerminatesAtSink({harness_out_out})` is `Violated`. A `verify` that
hands over the mode only when the harness has an environment place runs the hook's verifier
under `AlwaysAvailable` instead and proves it. -/
@[evidence forbids MOD_051]
theorem MOD_051_forbids_modeOnlyWithEnvs :
    ¬ MOD_051 (refInst strNaming) buildExScript refCompile refEnvVerify
      (mod051Wrong { mod051RefKnobs with run := mod051ModeOnlyWithEnvs }) := by
  intro hM
  obtain ⟨r, e, hr, he, hv⟩ := mod051_first (x := mod051Wrong
    { mod051RefKnobs with run := mod051ModeOnlyWithEnvs } mod051Closed
    ⟨[], [.terminatesAtSink ["harness_out_out"]]⟩ (some mod051IgnoreOwnEnv))
    (v := .proven "vacuous") (by decide)
  obtain ⟨I, envs, hI, hB, hp, h1, h2⟩ := mod051_entry hM hr he
  have h0 : harnessEnvs mod051Closed = [] := by decide
  rw [h0] at hp
  have henvs : envs = [] := List.Perm.eq_nil hp
  have hφ : e.1 = .terminatesAtSink ["harness_out_out"] := by simpa using h1
  have hline : ((refInst strNaming mod051Closed "sut").toOption.bind fun I =>
      (buildExScript (synthScript mod051Closed I)).toOption).map
      (fun c => (verifyOne refEnvVerify mod051IgnoreOwnEnv c []
        (.terminatesAtSink ["harness_out_out"])).verdict) = some .violated := by decide
  simp only [hI, hB, Except.toOption, Option.bind_some, Option.map_some] at hline
  rw [henvs, hφ] at h2
  rw [← h2, hv] at hline
  exact absurd hline (by decide)

/-- An operation that refuses every call is not covered: the forwarder with its token source
gets no report. -/
theorem mod051_rejectAll_not_covers :
    ¬ Mod051Covers (refInst strNaming) buildExScript refCompile
      (mod051RejectAll (refInst strNaming) buildExScript refCompile refEnvVerify) := by
  intro hc
  obtain ⟨I, hI, hc'⟩ := mod051_ok_of (x := refInst strNaming mod051Fwd "sut")
    (f := fun I => (buildExScript (synthScript mod051Fwd I)).toOption.map
      (fun c => refCompile c.toBuiltNet)) (b := some none) (by decide)
  obtain ⟨c, hcc, hC⟩ := mod051_ok_of hc'
  obtain ⟨r, hr⟩ := hc mod051Fwd (mod051H []) none I c (by decide) hI hcc hC
  revert hr
  simp only [mod051RejectAll]
  split <;> intro hr <;> cases hr

end Mutants

/-! ## MOD-051 (F): binding actions on a definition -/

section Bind

variable {N A : Type}

/-- **The body of a definition** as a built net: its places, its definitions (as transition
definitions) in order, its terminal places. -/
def subnetBody (S : SubnetDef N A) : BuiltNet N A :=
  ⟨S.places, S.defs.map (·.toTransDef), S.terminals⟩

/-- **The reference binding on a definition**: every body definition bound with the resolver by
its own, unprefixed name ([CORE-042] `bindWith`); its place correspondence, the name, the places,
the ports and the channels kept. -/
def refDefBind (S : SubnetDef N A) (r : String → Option (Act A)) : SubnetDef N A :=
  { S with defs := S.defs.map fun d => { d with toTransDef := d.toTransDef.bindWith r } }

/-- The map form on a definition as Rust reads it: an omitted name keeps its action. -/
def refDefBindMapKeep (S : SubnetDef N A) (m : String → Option (Act A)) : SubnetDef N A :=
  refDefBind S (mapKeep m)

/-- The map form on a definition as Java and TypeScript read it: an omitted name gets
passthrough. -/
def refDefBindMapClobber (S : SubnetDef N A) (m : String → Option (Act A)) : SubnetDef N A :=
  refDefBind S (mapClobber m)

/- The reference definition bindings are the witness models of MOD-051's binding block. -/
#spec_witness refDefBind
#spec_witness refDefBindMapKeep
#spec_witness refDefBindMapClobber

end Bind

requirement MOD_051_bind
  id "MOD-051"
  title "Binding actions on a subnet definition"
  kind F
  scope "bindActions (both forms) on a subnet definition in Java, TypeScript and Rust; Python's bind_actions on a definition rides on the Rust one"
  source verbatim "spec/11-modular-composition.md"
  quote "*When* actions are bound on a subnet definition, in either form, the new definition *shall* have the name, the ports and the channels of the original definition and the place correspondence ([MOD-031]) of each of its transitions, in the same order."
        "*When* actions are bound on a subnet definition with a resolver or a mapping, the body of the new definition *shall* be the net that binding the same resolver or mapping on the original body gives at net level ([CORE-042]), so the resolver or the mapping is keyed by the definition's own, unprefixed transition names."
  reading "For every net-level resolver binding Bind and map binding BindMap of CORE-042, and every definition-level resolver binding DBind and map binding DBindMap:"
          "for every definition S and resolver or map r, both DBind S r and DBindMap S r have S's name, ports and channels, and the place correspondences of S's definitions, position by position;"
          "for every S and resolver r, the body of DBind S r is Bind applied to the body of S with r;"
          "for every S and map m, the body of DBindMap S m is BindMap applied to the body of S with m."
  assumes "A definition-level binding is a function from a subnet definition (SubnetDef: name, places, transition definitions with their place correspondence, terminal places, ports, channels) and a resolver or map to a definition; its body (subnetBody) is the built net of its places, transition definitions and terminal places. Every runtime binds a definition by binding its body at net level and keeping the interface (rust/libpetri-core/src/subnet_def.rs:181-204, java/src/main/java/org/libpetri/core/SubnetDef.java:399-436, typescript/src/core/subnet-def.ts SubnetDef.bindActions, bindActionsWithResolver and withBody); Python binds through the Rust one (rust/libpetri-py/src/model.rs, PySubnetDef::bind_actions). Java and TypeScript re-point each channel at the rebuilt transition of the same name; a channel is its transition's name here, so it is kept unchanged. The parameter type is not modelled (Rust copies param_type)."
          "Lines 2 and 3 are 'mirroring the net-level operation of [CORE-042] with the same argument forms (mapping and resolver) and, per form, the same treatment of transitions it does not name, divergence included' and 'It is keyed by the definition's own, unprefixed transition names': Bind and BindMap are the implementation's own net-level bindings, which CORE-042 constrains (its line 5 carries the divergence: Rust keeps an omitted transition's action, Java and TypeScript substitute passthrough), and the body holds the definition's own names. Both readings meet the block (MOD_051_bind_reference_keep, MOD_051_bind_reference_clobber). A binding keyed by prefixed names is killed (MOD_051_bind_forbids_prefixedKeys), and so is a map form that ignores the map (MOD_051_bind_forbids_ignoreMap)."
          "Line 1 is 'returns a **new** definition whose ports, channels and parameters are unchanged'; the name, the places and the terminal places are kept through line 2, since CORE-042 keeps a net's places and terminal places. The place correspondence of MOD-031 is carried forward by the net-level rebuild in every runtime (CORE-042's assumes); a binding that drops the ports is killed (MOD_051_bind_forbids_dropPorts). 'The receiver is not modified' holds of every binding in the model, a function on immutable values, as in CORE-042."
          "'Instances created from the new definition carry the bound actions as their shared defaults ([MOD-030])' is a consequence: instantiation renames and keeps every action (TransDef.map_kept), so an instance of the bound definition carries the bound actions (mod051_bind_inst). 'The [CORE-043] check in `verify` applies to the bound definition as to any other' is line 3 of MOD_051, which ranges over every definition: binding a hand-written action to the forwarder's passthrough transition lets verify run (MOD_051_bind_nonvacuous)."
          "AC8 (bindActions on a definition returns a new definition whose instances carry the bound actions, keyed by unprefixed names; the receiver's instances keep the old ones; ports and parameters are unchanged) is lines 1 to 3 with mod051_bind_inst; the receiver's instances keep the old actions because the receiver is unchanged."
          "The block is relative to Bind and BindMap and does not require them to meet CORE-042: on its own it is met by a definition binding that changes nothing, paired with a Bind that changes nothing. Its force comes from reading Bind and BindMap as the implementation's own net-level bindings, which CORE_042 constrains; that conjunction is made where the two blocks are read together, at consistency level, and the forbids evidence here fixes Bind to the reference refBind."
  signoff "2026-11-13 6a9324aa9087148c ai"
  statement : ∀ {N A : Type}, (BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) →
      (BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) →
      (SubnetDef N A → (String → Option (Act A)) → SubnetDef N A) →
      (SubnetDef N A → (String → Option (Act A)) → SubnetDef N A) → Prop :=
    fun Bind BindMap DBind DBindMap =>
      (∀ S r, ∀ f ∈ [DBind, DBindMap],
        (f S r).name = S.name ∧ (f S r).ports = S.ports ∧ (f S r).chans = S.chans ∧
        (f S r).defs.map (·.corr) = S.defs.map (·.corr)) ∧
      (∀ S r, subnetBody (DBind S r) = Bind (subnetBody S) r) ∧
      (∀ S m, subnetBody (DBindMap S m) = BindMap (subnetBody S) m)

/- The pinned readable form of MOD-051's binding block. -/
/--
info: def Libpetri.Spec.MOD_051_bind : {N A : Type} →
  (BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) →
    (BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) →
      (SubnetDef N A → (String → Option (Act A)) → SubnetDef N A) →
        (SubnetDef N A → (String → Option (Act A)) → SubnetDef N A) → Prop :=
fun {N A} Bind BindMap DBind DBindMap =>
  (∀ (S : SubnetDef N A) (r : String → Option (Act A)),
      ∀ f ∈ [DBind, DBindMap],
        (f S r).name = S.name ∧
          (f S r).ports = S.ports ∧
            (f S r).chans = S.chans ∧ List.map (fun x => x.corr) (f S r).defs = List.map (fun x => x.corr) S.defs) ∧
    (∀ (S : SubnetDef N A) (r : String → Option (Act A)), subnetBody (DBind S r) = Bind (subnetBody S) r) ∧
      ∀ (S : SubnetDef N A) (m : String → Option (Act A)), subnetBody (DBindMap S m) = BindMap (subnetBody S) m
-/
#guard_msgs in #print MOD_051_bind

section BindEvidence

variable {N A : Type}

/-- The reference binding on a definition is the reference binding on its body. -/
theorem refDefBind_body (S : SubnetDef N A) (r : String → Option (Act A)) :
    subnetBody (refDefBind S r) = refBind (subnetBody S) r := by
  simp [subnetBody, refDefBind, refBind, Function.comp_def]

/-- The reference binding on a definition keeps the interface and the correspondences. -/
theorem refDefBind_iface (S : SubnetDef N A) (r : String → Option (Act A)) :
    (refDefBind S r).name = S.name ∧ (refDefBind S r).ports = S.ports ∧
      (refDefBind S r).chans = S.chans ∧
      (refDefBind S r).defs.map (·.corr) = S.defs.map (·.corr) := by
  simp [refDefBind, Function.comp_def]

/-- ✓ **The reference meets the binding block with the map read as Rust reads it.** Example:
binding a hand-written action to `work` on the forwarder binds `work` in the body, by that
unprefixed name, and keeps the ports `in` and `out`; a name the map omits keeps its action. -/
@[evidence holds MOD_051_bind]
theorem MOD_051_bind_reference_keep :
    MOD_051_bind (refBind (N := N) (A := A)) refBindMapKeep refDefBind refDefBindMapKeep := by
  refine ⟨fun S r f hf => ?_, refDefBind_body, fun S m => refDefBind_body S (mapKeep m)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact refDefBind_iface S r
  · exact refDefBind_iface S (mapKeep r)

/-- ✓ **The reference meets the binding block with the map read as Java and TypeScript read
it.** Example: binding the forwarder with a map that omits `work` leaves `work` on passthrough,
as the same map does on a net. -/
@[evidence holds MOD_051_bind]
theorem MOD_051_bind_reference_clobber :
    MOD_051_bind (refBind (N := N) (A := A)) refBindMapClobber refDefBind
      refDefBindMapClobber := by
  refine ⟨fun S r f hf => ?_, refDefBind_body, fun S m => refDefBind_body S (mapClobber m)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact refDefBind_iface S r
  · exact refDefBind_iface S (mapClobber r)

/-- **Instances carry the bound actions** ([MOD-030], AC8). In every model of the binding
block, the instance of a bound definition under prefix `p` carries, position by position, the
actions the net-level binding gives the body: binding `work` on the forwarder and instantiating
under `a` gives `a/work` the bound action. -/
@[evidence cites "MOD-051" "AC8: bindActions on a definition returns a new definition whose instances carry the bound actions, keyed by unprefixed names: in every model of the MOD_051_bind block, the instance of the bound definition carries the actions the net-level binding gives the body, position by position"]
theorem mod051_bind_inst {Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A}
    {DBind DBindMap : SubnetDef N A → (String → Option (Act A)) → SubnetDef N A}
    (hM : MOD_051_bind Bind BindMap DBind DBindMap) (Nm : Naming N) (S : SubnetDef N A)
    (r : String → Option (Act A)) (p : String) :
    (renamedInstance Nm (DBind S r) p).defs.map (·.action) =
      (Bind (subnetBody S) r).trans.map (·.action) := by
  rw [← hM.2.1 S r]
  simp [subnetBody, renamedInstance, List.map_map, Function.comp_def, CDef.map_toTransDef,
    TransDef.map]

/-- The forwarder's `work` bound to a hand-written action. -/
def mod051BindWork : String → Option (Act Unit) := fun n => if n = "work" then some (.other ()) else none

set_option maxRecDepth 20000 in
/-- ✓ **Binding on a definition, worked.** The forwarder whose `work` keeps passthrough is
refused by `verify` ([CORE-043]); binding a hand-written action to `work`, by its unprefixed
name, gives a definition with the same ports whose instance under `sut` carries that action on
`sut/work`, and `verify` now returns a report. -/
@[evidence nonvacuous MOD_051_bind]
theorem MOD_051_bind_nonvacuous :
    ((refDefBind mod051FwdPT mod051BindWork).defs.map (·.action)) = [.other ()] ∧
    (refDefBind mod051FwdPT mod051BindWork).ports.map (·.name) = ["in", "out"] ∧
    ((renamedInstance strNaming (refDefBind mod051FwdPT mod051BindWork) "sut").defs.map
      (fun d => (d.core.name, d.action))) = [("sut/work", .other ())] ∧
    (mod051RefEx mod051FwdPT (mod051H []) none).toOption.isSome = false ∧
    (mod051RefEx (refDefBind mod051FwdPT mod051BindWork) (mod051H []) none).toOption.isSome =
      true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A binding on a definition that drops the ports. -/
def mod051DropPorts (S : SubnetDef N A) (r : String → Option (Act A)) : SubnetDef N A :=
  { refDefBind S r with ports := [] }

/-- ✗ **The ports are kept** (line 1). Example: a binding that rebuilds the forwarder without its
ports `in` and `out` leaves nothing to bind at compose. -/
@[evidence forbids MOD_051_bind]
theorem MOD_051_bind_forbids_dropPorts :
    ¬ MOD_051_bind (refBind (N := String) (A := Unit)) refBindMapKeep mod051DropPorts
      refDefBindMapKeep := by
  intro hM
  have h := congrArg (fun ps : List (Port String) => ps.length)
    (hM.1 mod051Fwd mod051BindWork mod051DropPorts (by simp)).2.1
  simp [mod051DropPorts, refDefBind, mod051Fwd] at h

/-- A binding on a definition keyed by prefixed names (`<definition>/<transition>`). -/
def mod051PrefixedKeys (S : SubnetDef String A) (r : String → Option (Act A)) :
    SubnetDef String A :=
  refDefBind S (fun n => r (S.name ++ "/" ++ n))

/-- ✗ **Keyed by unprefixed names** (line 2). Example: a resolver that answers `work` binds the
forwarder's `work` at net level; a binding that asks for `fwd/work` gets no answer and leaves
`work` on passthrough. -/
@[evidence forbids MOD_051_bind]
theorem MOD_051_bind_forbids_prefixedKeys :
    ¬ MOD_051_bind (refBind (N := String) (A := Unit)) refBindMapKeep mod051PrefixedKeys
      refDefBindMapKeep := by
  intro hM
  have h := congrArg (fun b : BuiltNet String Unit => b.trans.map (·.action))
    (hM.2.1 mod051FwdPT mod051BindWork)
  revert h
  decide

/-- A map form on a definition that ignores the map. -/
def mod051IgnoreMap (S : SubnetDef N A) (_ : String → Option (Act A)) : SubnetDef N A := S

/-- ✗ **The map form binds** (line 3). Example: a map naming `work` binds it on the forwarder's
body at net level; a map form that ignores the map leaves `work` on passthrough. -/
@[evidence forbids MOD_051_bind]
theorem MOD_051_bind_forbids_ignoreMap :
    ¬ MOD_051_bind (refBind (N := String) (A := Unit)) refBindMapKeep refDefBind
      mod051IgnoreMap := by
  intro hM
  have h := congrArg (fun b : BuiltNet String Unit => b.trans.map (·.action))
    (hM.2.2 mod051FwdPT mod051BindWork)
  revert h
  decide

end BindEvidence

end Libpetri.Spec
