import Libpetri.Spec.Registry
import Libpetri.Reference.NuMint
import Libpetri.Spec.Text.NU_011

set_option linter.missingDocs true

/-!
# NU-011: Resume-Safe Fresh-Name Minting (`spec/12-nu-nets.md`)

NU-011 keeps names minted after a restore ([CORE-073]) apart from the names of the earlier run
segments. All four runtimes do it with a **scope**: every name an executor mints is
`<transition>#<scope>:<n>`, the scope is pinned by the host or drawn at random once per executor,
and `<n>` is one counter per executor that starts at zero.

Four blocks share the ID (ruling D56 (a)):

* `NU_011_format` (kind F), over a minter `Sy : MintSys` and a scope check `V : ScopeCheck`: a
  scope that is empty or holds `:` or `#` is rejected, every other scope is accepted (a blank one
  included), and under an accepted scope `s` the `i`-th `freshName()` call of the executor, by
  transition `t`, returns `mintName t s i`, `i` in decimal.
* `NU_011_lineage` (kind B), over the same pair: two executions under two different accepted
  scopes share no minted name. It follows from the format block by the parse rule
  (`nu011_lineage_of_format`), and it is the body's "MUST NOT collide".
* `NU_011_default` (kind B), over the default draw `D : Nat → String → Prop` (`D k s`: the `k`-th
  executor of a process, given no scope, may draw `s`): every draw is 32 lowercase hexadecimal
  characters. That no construction index fixes the draw, so the default is not the run
  identifier, is an existence clause: the coverage conjunct `DefaultUnfixed` of
  `joint_nu_sketch`.
* `NU_011_host` (kind A), over the executions of one restore lineage whose scope the host pinned:
  two of them share a scope only when one replays the other, the same segment with the same
  `freshName()` calls. Under it, two executions share a minted name only when one replays the
  other (`nu011_host_replay`), and without a replay every name is minted once
  (`nu011_host_distinct`, `nu011_lineage_nodup`).

The witnesses are `refMintSys` and `refValidScope` (`Reference/NuMint.lean`) and
`refDefaultDraw` (below). The existence half ("every `freshName()` call is answered") is not a
block line: a minter with no mint step meets every line here, so it is the coverage conjunct
`MintTotal` of `Spec/ConsistencyNu.lean`, the one NU-010 names (`nu011_noSepTrans_needs_cover`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

/-! ## NU-011, scope check and name format -/

requirement NU_011_format
  id "NU-011"
  title "Resume-Safe Fresh-Name Minting (scope check and name format)"
  kind F
  scope "every executor that mints under the scope mechanism (Rust, Java, TypeScript; Python through Rust)"
  source verbatim "spec/12-nu-nets.md"
  covers NU_011.s1, NU_011.s2, NU_011.s3
  reading "Let V be the scope check (V s = true: the executor accepts the scope s when it is configured) and Sy the minter (MintRun Sy (Sy.init s) evs xs: an executor whose scope is s answers the events evs, freshName() calls and firing boundaries, with the names xs, one per call)."
          "For every scope s that is empty or holds ':' or '#', V rejects s."
          "For every scope s that is not empty and holds neither ':' nor '#', V accepts s."
          "For every scope s that V accepts and every run of Sy from the initial state for s, the names returned are, call by call, mintName t s i for the i-th call (from 0), t being the transition that made it; mintName writes i in decimal (Nat.repr)."
  assumes "The model is the pair (Sy, V) of Reference/NuMint.lean. V : ScopeCheck is the check made when the executor is configured. Sy : MintSys is an abstract minter: a state type, an initial state per scope, a mint relation (state, calling transition, returned name, next state) and a step at each firing boundary; MintRun interleaves freshName() calls and firing boundaries, so two calls in one firing and a counter reset per firing are both observable. The witnesses are refValidScope (rust/libpetri-runtime/src/executor_core/scope.rs validate_execution_scope; java/src/main/java/org/libpetri/core/internal/ExecutionScopes.java requireValid, called by BitmapNetExecutor.Builder.executionScope in BitmapNetExecutor.java; typescript/src/runtime/executor-support.ts resolveExecutionScope) and refMintSys, one counter per executor shared by every transition, read when the action calls the minter (Executor::fresh_name_fn in rust/libpetri-runtime/src/executor_core/executor.rs, fetch_add on fresh_name_counter and format {name}#{scope}:{n}; java BitmapNetExecutor.java, the freshNameCounter field and the fresh-name supplier fireTransition sets; typescript/src/runtime/bitmap-net-executor.ts, the freshNameCounter field and the fresh-name supplier fireTransition sets). Every runtime writes the counter in decimal (Rust {n} on a u64, Java and TypeScript string concatenation of a number)."
          "The last line is one counter for the whole executor, counted across firings: a counter kept per transition (NU_011_format_forbids_perTrans, the slip of building the counter inside Rust's per-transition fresh_name_fn cache or TypeScript's freshNameSuppliers instead of sharing fresh_name_counter) and a counter reset at every firing (NU_011_format_forbids_perFiring, a counter on Java's per-firing TransitionContext instead of the executor field) both break it, although both still mint names that are distinct and carry the scope, so neither NU-010's uniqueness nor NU_011_lineage sees them."
          "Ruling D56 (a): the names are keyed on the order of the freshName() calls, not on the firing order; a firing boundary changes nothing in refMintSys. 'For a fixed scope (or a fixed restored high-water mark) and a fixed order of freshName() calls, the minted sequence MUST be reproducible', 'the counter <n> MUST NOT be random' and 'a scope the host pinned MUST be used verbatim, with nothing random mixed into it or into the sequence minted under it' are the last line: the names are a function of the scope and the calls (nu011_replay, nu011_calls_only). A minter that may return any counter (NU_011_format_forbids_randomCounter) and one that mixes a salt into the pinned scope (NU_011_format_forbids_salted) break it. The sentence 'The firing order fixes the order of the calls when at most one minting action is in flight at a time, or when every call is made inline by a synchronous action' is not a line: it tells a host when the firing order is enough, and it rests on every runtime calling the action inline when the transition fires (java BitmapNetExecutor.fireTransition through ExecutorSupport.executeAction; typescript fireTransition in bitmap-net-executor.ts through executeAction in executor-support.ts; rust Executor::fire_transition_async in executor_core/executor.rs for a synchronous action, which Python rides), while a call an asynchronous action makes after it yields lands in the order the completions decide."
          "Scope: 'An implementation using the scope mechanism mints <transition>#<scope>:<n>, where <n> is a per-executor counter from zero.' All four runtimes use the scope mechanism. The other mechanism the body names (carrying the minter's high-water mark in the snapshot) is used by no runtime and is outside every NU-011 block; a MintSys over another state type can model it, but it would not meet the last line, so the body's unqualified non-collision MUST has a formal statement for the scope mechanism only (NU_011_lineage). The sentence on deriving the floor by scanning the restored marking is about that mechanism and is not a line."
          "'A host-supplied scope MUST be rejected when the executor is configured, not at the first mint': V is that check, and the model has no other point where a scope could be refused; that the runtimes run it at configuration rests on the call sites cited above, not on a theorem (open: plan clash nu S9). Which call raises it (the Java builder setter, the TypeScript constructor, Rust's set_execution_scope and every builder that takes a scope) is API shape, kind Q. How it is raised (IllegalArgumentException, Error, Python ValueError, a Rust panic) is configuration, kind N. 'The separators are rejected rather than escaped' and 'Empty means length zero' are the first two lines; 'an implementation MUST NOT trim the scope or test it for blankness' is the second line, which a check that refuses a blank scope breaks (NU_011_format_forbids_blankTest)."
          "'Rejecting : alone is not enough': a check that accepts '#' breaks the first line (NU_011_format_forbids_hashOk) and the lineage block (NU_011_lineage_forbids_hashOk), on the spec's example: transition a under scope b#c and transition a#b under scope c both mint a#b#c:0 (nu011_collision). The parse rule ('the last : splits off the counter, and the last # before it splits off the scope') is a fact about the fixed format given the '#' ban and the decimal counter, which holds no ':': nu011_parse, and AC6's worked example nu011_ac6. The ':' ban is load-bearing only in the first line (NU_011_format_forbids_colonOk)."
          "The default scope is NU_011_default's; that a drawn default is an accepted scope (nu011_default_draw_accepted) is what lets the last line and NU_011_lineage cover default-scope names. The advice that a pinned scope stay within the Basic Multilingual Plane is advice to the host, not a validation (N). AC6 (an empty scope, a scope with ':' and one with '#' are rejected at configuration, a whitespace-only scope is accepted, and a name minted by a transition whose own name holds '#' and ':' splits back) is the first two lines with nu011_ac6; worked in NU_011_format_nonvacuous. AC1, AC2 and AC4 are NU_011_lineage's, AC3 NU_011_host's, AC5 NU_011_default's."
  signoff "2026-11-13 e991c428ff685d54 ai"
  statement : MintSys → ScopeCheck → Prop :=
    fun Sy V =>
      (∀ s : String, (s = "" ∨ ':' ∈ s.toList ∨ '#' ∈ s.toList) → V s = false) ∧
      (∀ s : String, s ≠ "" → ':' ∉ s.toList → '#' ∉ s.toList → V s = true) ∧
      (∀ s, V s = true → ∀ evs xs, MintRun Sy (Sy.init s) evs xs →
        xs = (calls evs).mapIdx fun i t => mintName t s i)

/- The pinned readable form of NU_011_format: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_011_format : MintSys → ScopeCheck → Prop :=
fun Sy V =>
  (∀ (s : String), s = "" ∨ ':' ∈ s.toList ∨ '#' ∈ s.toList → V s = false) ∧
    (∀ (s : String), s ≠ "" → ':' ∉ s.toList → '#' ∉ s.toList → V s = true) ∧
      ∀ (s : String),
        V s = true →
          ∀ (evs : List MintEv) (xs : List String),
            MintRun Sy (Sy.init s) evs xs → xs = List.mapIdx (fun i t => mintName t s i) (calls evs)
-/
#guard_msgs in #print NU_011_format

/-! ## NU-011, different scopes, different names -/

requirement NU_011_lineage
  id "NU-011"
  title "Resume-Safe Fresh-Name Minting (different scopes, disjoint names)"
  kind B
  scope "every executor that mints under the scope mechanism; two executions of one restore lineage"
  source verbatim "spec/12-nu-nets.md"
  covers NU_011.s4
  reading "For every two different scopes s and s' that V accepts, every run of Sy from the initial state for s and every run of Sy from the initial state for s': no name returned by the first is returned by the second."
  assumes "The model is the pair (Sy, V), as for NU_011_format. The block follows from NU_011_format by the parse rule (nu011_lineage_of_format); it is stated on its own because it is the body's MUST and what resume safety rests on, and because a minter that ignores the host's scope and uses one scope per process breaks it (NU_011_lineage_forbids_perProcess): 'The restore lineage crosses processes', and the scope is the only state one segment hands to the next."
          "Ruling D56 (a): 'Names minted by an execution seeded from a restored marking MUST NOT collide with names minted by any other execution in the same restore lineage, other than a replay of the same segment (AC3), whether or not those names are still present in that marking' holds under the scope mechanism when the executions run under different scopes; the replay exception is NU_011_host's, whose formula lets two entries share a scope only when they run the same segment with the same calls (nu011_host_replay). Two runs under one pinned scope mint the same names (AC3), so the condition is the host's for pinned scopes (NU_011_host) and the random draw's for default ones (NU_011_default, with the kind Q claim that two draws differ). Within one execution, minted names are pairwise distinct by NU-010 (refRun_nodup); with this block and distinct scopes every name minted in a lineage is minted once (nu011_lineage_nodup). A name the host put into a token itself (a copied correlation id) is a host value, not a minted name, and is not covered (the mint contract of NU-010)."
          "AC1 (a resumed execution, under the default scope or a pinned scope other than the prior execution's, never mints the name n a prior execution minted into the restored marking) is the line with NU_011_host; worked in NU_011_lineage_nonvacuous and stated for any held name in refRun_fresh. AC4 (two concurrent executions restored from one snapshot, under the default scope or two different pinned scopes, mint disjoint name sets) is the line. AC2 (a restored token awaiting its sibling at a NU-020 join is not correlated with a freshly minted token) is nu011_ac2: a join correlates on name equality alone, and by the line no name of the resumed segment equals a name of an earlier one; the firing-level statement over the ν executor with restore (CORE-073), which would cite NU-020's enablement line directly, is stated by no block: CORE-073's blocks read executors with no ν firing kernel, and NU_020_enable reads the atomic ν firing, with no restore."
          "'Anything derived from a per-process counter restarts with the process' and the paragraph on processes describe why the default scope is random; the model has no process, and the per-process minter above is the forbidden shape here, the scope derived from the execution id the forbidden shape in NU_011_default. The test derivation is AC1, AC2 and AC4 under pinned and default scopes; 'No test may depend on how many executors the process constructed before it' is test guidance (Q)."
  signoff "2026-11-13 bacd928c2a3864eb ai"
  statement : MintSys → ScopeCheck → Prop :=
    fun Sy V => ∀ s s', V s = true → V s' = true → s ≠ s' →
      ∀ evs evs' xs xs', MintRun Sy (Sy.init s) evs xs → MintRun Sy (Sy.init s') evs' xs' →
        ∀ x ∈ xs, x ∉ xs'

/- The pinned readable form of NU_011_lineage. -/
/--
info: def Libpetri.Spec.NU_011_lineage : MintSys → ScopeCheck → Prop :=
fun Sy V =>
  ∀ (s s' : String),
    V s = true →
      V s' = true →
        s ≠ s' →
          ∀ (evs evs' : List MintEv) (xs xs' : List String),
            MintRun Sy (Sy.init s) evs xs → MintRun Sy (Sy.init s') evs' xs' → ∀ x ∈ xs, x ∉ xs'
-/
#guard_msgs in #print NU_011_lineage

/-! ## NU-011, the default scope -/

/-- The lowercase hexadecimal digits a default scope is written with. -/
def nu011_hexDigits : List Char := "0123456789abcdef".toList

/-- The reference default draw: the `k`-th executor of a process may draw any string of 32
lowercase hexadecimal characters, whatever `k` is. This is Rust's draw, two 64-bit outputs
written as `{:016x}{:016x}`, which Python rides. -/
def refDefaultDraw : Nat → String → Prop := fun _ s =>
  s.length = 32 ∧ ∀ c ∈ s.toList, c ∈ nu011_hexDigits

#spec_witness refDefaultDraw

/-- **The default draw is not fixed** (the coverage conjunct of NU-011's default scope): whatever
string is named, the `k`-th executor of a process may draw another one, so neither the
construction index nor anything computed from it determines the default scope. It is an
existence clause, so it is a conjunct of the consistency theorem (`joint_nu_sketch`), not a line
of `NU_011_default`. -/
def DefaultUnfixed (D : Nat → String → Prop) : Prop := ∀ k s, ∃ s', D k s' ∧ s' ≠ s

requirement NU_011_default
  id "NU-011"
  title "Resume-Safe Fresh-Name Minting (default scope)"
  kind B
  scope "every executor that is given no scope (Rust, Java, TypeScript; Python through Rust)"
  source verbatim "spec/12-nu-nets.md"
  covers NU_011.s5
  reading "Let D be the default draw (D k s: the k-th executor constructed in its process, given no scope, may run under the scope s)."
          "For every k and every s with D k s, s is 32 characters long and each of its characters is one of 0123456789abcdef."
  assumes "The model is the relation D : Nat → String → Prop, the scopes the k-th executor of a process can draw. The witness is refDefaultDraw, every 32-character lowercase hexadecimal string: Rust writes two 64-bit SipHash outputs of RandomState hashers keyed from the operating system's random source as {:016x}{:016x} (default_execution_scope in rust/libpetri-runtime/src/executor_core/scope.rs). Java (ExecutionScopes.random in java/src/main/java/org/libpetri/core/internal/ExecutionScopes.java, UUID.randomUUID() written as two zero-padded 16-digit lowercase hexadecimal halves, the UUID with its dashes stripped) and TypeScript (randomExecutionScope in typescript/src/runtime/executor-support.ts, crypto.randomUUID() with its dashes stripped, where it exists) draw a version-4 UUID, a smaller relation that fixes the version and variant digits; it meets both lines (nu011_uuidDraw_default). Where Web Crypto has no randomUUID, TypeScript writes 16 bytes of crypto.getRandomValues, and with no Web Crypto at all 16 bytes of Math.random, as 32 lowercase hexadecimal characters: that is refDefaultDraw itself (NU_011_default_reference, refDefaultDraw_unfixed)."
          "The clause 'which neither its construction order nor its run identifier determines' says that some other draw is possible, an existence clause, so it is not a line here: it is the coverage conjunct DefaultUnfixed of the consistency theorem (joint_nu_sketch, over the same D, witnessed by refDefaultDraw through refDefaultDraw_unfixed; Java's and TypeScript's UUID draw meets it too, nu011_uuidDraw_unfixed). The run identifier of TIME-015 is the reproducible per-process counter (AC#14), a function of the construction index k, so that conjunct is 'an implementation MUST NOT derive either from the other' for the default scope and AC5's 'not equal to it' (nu011_default_not_runId). The other direction, a run identifier derived from the default scope, is ruled out on the run identifier's side: EVT_002_executionId's model writes the ID as a function of the construction place k and the clock reading r alone, so an ID that depends on a random draw is not such an assignment, and every runtime draws it from a per-process counter (EXECUTION_ID_SEQ in rust/libpetri-runtime/src/executor_core/executor.rs, nextExecutionId in java/src/main/java/org/libpetri/runtime/ExecutorSupport.java and in typescript/src/runtime/executor-support.ts), never from the scope. A default equal to the execution id written in 32 hexadecimal digits, the earlier Java behaviour, meets NU_011_format and NU_011_lineage, and this block for every execution id below 16^32, but breaks the conjunct (nu011_fromId_fixed): the process that persisted a snapshot and the process that resumes it both mint the same first name (nu011_fromId_merge), the silent merge of AC5's last sentence. A draw written with the dashes of a UUID breaks the line (NU_011_default_forbids_dashed)."
          "The conjunct is a property of the set of possible draws, not of one run: randomness is not a safety property of a single execution, so it states the part a relation can see, that the construction order does not determine the draw. Kind Q (tests, not proven): that two draws differ ('The default scope MUST be unique across processes', AC5 'different for every executor'), which holds with overwhelming probability and not in every run, and 'at least 122 bits are random', which a relation over strings cannot count; that a pinned scope never equals a drawn default is the same claim, since the default is internal and random. Rust's draw is two SipHash outputs under RandomState keys taken from the operating system's random source once per thread (each later RandomState::new() on the thread adds one to the key), with the process id, a draw counter and the clock folded in: a 128-bit value computed under a 128-bit operating-system random key, drawn once per executor (get_or_init), which this block reads as drawn from the platform's random source; like the bit count, that is kind Q."
          "The paragraph on observability ('The default scope MAY be entirely internal', and 'MUST NOT be read as required to merely to satisfy this requirement') constrains no line: the model never asks whether a draw is published. A drawn default is an accepted scope (nu011_default_draw_accepted), so NU_011_format and NU_011_lineage cover default-scope names. AC5 (an executor given no scope mints names whose scope is 32 lowercase hexadecimal characters, different for every executor and not the run identifier) is the line for the rendering, the coverage conjunct DefaultUnfixed for 'not equal to it', and kind Q for 'different for every executor'; worked in NU_011_default_nonvacuous."
  signoff "2026-11-13 e386109e5003829f ai"
  statement : (Nat → String → Prop) → Prop :=
    fun D => ∀ k s, D k s → s.length = 32 ∧ ∀ c ∈ s.toList, c ∈ nu011_hexDigits

/- The pinned readable form of NU_011_default. -/
/--
info: def Libpetri.Spec.NU_011_default : (ℕ → String → Prop) → Prop :=
fun D => ∀ (k : ℕ) (s : String), D k s → s.length = 32 ∧ ∀ c ∈ s.toList, c ∈ nu011_hexDigits
-/
#guard_msgs in #print NU_011_default

/-! ## NU-011, the host of a restore lineage -/

requirement NU_011_host
  id "NU-011"
  title "Resume-Safe Fresh-Name Minting (host of a restore lineage)"
  kind A
  scope "hosts that pin scopes for the executions of a restore lineage"
  source verbatim "spec/12-nu-nets.md"
  covers NU_011.s6
  reading "Let es list the executions of one restore lineage whose scope the host pinned, each as (s, k, ts): its scope s, the segment k it runs, and the calling transitions ts of its freshName() calls in order. A segment is one stretch of the lineage's history: two executions that run alongside each other run two segments, even from one marking; an execution that starts from another marking than the one a segment started from does not run that segment, whatever calls it makes; and a replay, which runs after the segment it re-runs, not alongside it, and from the marking that segment started from, runs that segment."
          "For every two entries of es with the same scope, the segment and the calls are the same."
  assumes "Ruling D56 (a). The block is an assumption on the host (kind A), not a behaviour of the executor: a pinned scope is used verbatim (NU_011_format), so a resumed execution pinned to the scope of the segment before it mints that segment's names again (nu011_host_needed). The Rust runtime documents the same promise ('a pinned one is the host's promise: two executions in one restore lineage MUST NOT share a scope', the doc of Executor::set_execution_scope in rust/libpetri-runtime/src/executor_core/executor.rs). The block speaks of pinned scopes only: default scopes are NU_011_default's, and that two defaults, or a default and a pinned scope, differ is the kind Q claim there."
          "The replay exception is in the formula: two entries with one scope run the same segment with the same calls. A replay that makes other calls breaks the block (NU_011_host_forbids_divergentReplay): under the one scope its second call takes the counter the segment's second call took, for another token. 'After it and not alongside it' and 'from the marking that segment started from' are carried by the segment numbering of the reading (an execution that runs alongside another runs a segment of its own, and one that starts from another marking than a segment started from does not run that segment), not by a clock or a marking in the model: which segment an execution runs is the host's bookkeeping, and the model takes it as given. The marking condition is load-bearing: names are a function of the scope and the calls (nu011_calls_only), so an execution that re-made segment 0's calls under its scope from a later marking would mint segment 0's names into a marking that may still hold them."
          "What the assumption buys: under NU_011_format, two executions of the lineage that share a minted name run the same segment with the same calls and mint the same names (nu011_host_replay), so the only names two executions share are the ones a replay reproduces. Without a replay the pinned scopes are pairwise distinct (nu011_host_distinct), and with distinct scopes every name of the lineage is minted once (nu011_lineage_nodup): AC4, and for the names minted into a restored marking AC1 (refRun_fresh)."
          "AC3 (for a fixed scope and a fixed order of freshName() calls, two runs from the same restored marking mint the identical name sequence) is NU_011_format's last line (nu011_replay); such a run is the replay this block excepts. That two runs under one scope mint equal names is the reason the non-collision of NU_011_lineage needs different scopes."
  signoff "2026-11-13 98972dec45836fc0 ai"
  statement : List (String × Nat × List String) → Prop :=
    fun es => ∀ e ∈ es, ∀ e' ∈ es, e.1 = e'.1 → e.2 = e'.2

/- The pinned readable form of NU_011_host. -/
/--
info: def Libpetri.Spec.NU_011_host : List (String × ℕ × List String) → Prop :=
fun es => ∀ e ∈ es, ∀ e' ∈ es, e.1 = e'.1 → e.2 = e'.2
-/
#guard_msgs in #print NU_011_host

/-! ## Holds -/

/-- ✓ The reference pair meets the format block: `refValidScope` rejects an empty scope and one
holding `:` or `#` and accepts every other, and the reference minter returns `<t>#<s>:<i>` for
the `i`-th call, whatever the firing boundaries. -/
@[evidence holds NU_011_format]
theorem NU_011_format_reference : NU_011_format refMintSys refValidScope := by
  refine ⟨fun s h => ?_, fun s h1 h2 h3 => (refValidScope_iff s).2 ⟨h1, h2, h3⟩,
    fun _ _ _ _ h => refRun_names h⟩
  cases hv : refValidScope s
  · rfl
  · obtain ⟨h1, h2, h3⟩ := (refValidScope_iff s).1 hv
    rcases h with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3

/-- The names of a run that meets the format block were minted under its scope. -/
theorem nu011_mintedUnder {Sy : MintSys} {V : ScopeCheck} (h : NU_011_format Sy V) {s : String}
    (hs : V s = true) {evs : List MintEv} {xs : List String}
    (hr : MintRun Sy (Sy.init s) evs xs) : ∀ x ∈ xs, MintedUnder s x := by
  intro x hx
  rw [h.2.2 s hs evs xs hr, List.mem_mapIdx] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact ⟨_, i, rfl⟩

/-- A scope the format block's check accepts holds no `#`. -/
theorem nu011_noHash {Sy : MintSys} {V : ScopeCheck} (h : NU_011_format Sy V) {s : String}
    (hs : V s = true) : '#' ∉ s.toList := fun hm => by
  have := h.1 s (Or.inr (Or.inr hm))
  rw [hs] at this
  cases this

/-- The lineage block follows from the format block: two names minted under two accepted scopes
that hold no `#` are equal only when the scopes are, by the parse rule. -/
@[evidence cites "NU-011" "With # banned as well, a minted name parses uniquely whatever the transition name contains: two executions under different accepted scopes never mint one name"]
theorem nu011_lineage_of_format {Sy : MintSys} {V : ScopeCheck} (h : NU_011_format Sy V) :
    NU_011_lineage Sy V := by
  intro s s' hs hs' hne evs evs' xs xs' hr hr' x hx hx'
  exact hne (mintedUnder_unique (nu011_noHash h hs) (nu011_noHash h hs')
    (nu011_mintedUnder h hs hr x hx) (nu011_mintedUnder h hs' hr' x hx'))

/-- ✓ The reference pair meets the lineage block: two reference runs under two different
accepted scopes share no name (`refRun_disjoint`). -/
@[evidence holds NU_011_lineage]
theorem NU_011_lineage_reference : NU_011_lineage refMintSys refValidScope :=
  fun _ _ hs hs' hne _ _ _ _ hr hr' =>
    refRun_disjoint (refValidScope_noHash hs) (refValidScope_noHash hs') hne hr hr'

/-- Two different 32-character hexadecimal strings, used to show that a draw is not fixed. -/
def nu011_hex0 : String := "00000000000040008000000000000000"

/-- The second of the two strings. -/
def nu011_hex1 : String := "00000000000040008000000000000001"

/-- ✓ The reference draw meets the default block: every draw is 32 lowercase hexadecimal
characters. -/
@[evidence holds NU_011_default]
theorem NU_011_default_reference : NU_011_default refDefaultDraw := fun _ _ h => h

/-- The reference draw is not fixed: whatever string you name, the executor may draw another
one. -/
theorem refDefaultDraw_unfixed : DefaultUnfixed refDefaultDraw := by
  intro _ s
  by_cases h : s = nu011_hex0
  · exact ⟨nu011_hex1, by unfold refDefaultDraw nu011_hex1; decide,
      by rw [h]; unfold nu011_hex0 nu011_hex1; decide⟩
  · exact ⟨nu011_hex0, by unfold refDefaultDraw nu011_hex0; decide, fun h' => h h'.symm⟩

/-- The draw of Java and TypeScript: a version-4 UUID with its dashes removed, so the 13th
character is `4` and the 17th is one of `8`, `9`, `a`, `b`. -/
def nu011_uuidDraw : Nat → String → Prop := fun k s =>
  refDefaultDraw k s ∧ s.toList[12]? = some '4' ∧
    s.toList[16]? ∈ [some '8', some '9', some 'a', some 'b']

/-- The version-4 UUID draw of Java and TypeScript also meets the default block: it is a smaller
set of 32-character hexadecimal strings. -/
theorem nu011_uuidDraw_default : NU_011_default nu011_uuidDraw := fun _ _ h => h.1

/-- The version-4 UUID draw still holds more than one string, so it is not fixed either. -/
theorem nu011_uuidDraw_unfixed : DefaultUnfixed nu011_uuidDraw := by
  intro _ s
  by_cases h : s = nu011_hex0
  · exact ⟨nu011_hex1, by unfold nu011_uuidDraw refDefaultDraw nu011_hex1; decide,
      by rw [h]; unfold nu011_hex0 nu011_hex1; decide⟩
  · exact ⟨nu011_hex0, by unfold nu011_uuidDraw refDefaultDraw nu011_hex0; decide,
      fun h' => h h'.symm⟩

/-! ## Consequences the assumes lines name -/

/-- **Replay.** Under the format block, one accepted scope and one sequence of `freshName()`
calls give one name sequence: a run that re-runs a segment under its pinned scope mints the same
names (AC3). -/
@[evidence cites "NU-011" "AC3: for a fixed scope and a fixed order of freshName() calls, two runs from the same restored marking mint the identical name sequence"]
theorem nu011_replay {Sy : MintSys} {V : ScopeCheck} (h : NU_011_format Sy V) {s : String}
    (hs : V s = true) {evs : List MintEv} {xs ys : List String}
    (h1 : MintRun Sy (Sy.init s) evs xs) (h2 : MintRun Sy (Sy.init s) evs ys) : xs = ys := by
  rw [h.2.2 s hs evs xs h1, h.2.2 s hs evs ys h2]

/-- Firing boundaries do not change the names: two event sequences with the same calls, in the
same order, give the same names (ruling D56 (a)). -/
theorem nu011_calls_only {Sy : MintSys} {V : ScopeCheck} (h : NU_011_format Sy V) {s : String}
    (hs : V s = true) {evs evs' : List MintEv} {xs ys : List String}
    (hc : calls evs = calls evs')
    (h1 : MintRun Sy (Sy.init s) evs xs) (h2 : MintRun Sy (Sy.init s) evs' ys) : xs = ys := by
  rw [h.2.2 s hs evs xs h1, h.2.2 s hs evs' ys h2, hc]

/-- **The parse rule.** Two names minted under accepted scopes are equal only when transition,
scope and counter are, whatever the transition names hold. -/
@[evidence cites "NU-011" "the last : splits off the counter, and the last # before it splits off the scope; everything in front is the transition name"]
theorem nu011_parse {t t' s s' : String} {n n' : Nat} (hs : refValidScope s = true)
    (hs' : refValidScope s' = true) (h : mintName t s n = mintName t' s' n') :
    t = t' ∧ s = s' ∧ n = n' :=
  mintName_inj_of_valid hs hs' h

/-- Why `#` is banned as well as `:`: transition `a` under scope `b#c` and transition `a#b` under
scope `c` both mint `a#b#c:0`. -/
@[evidence cites "NU-011" "Transition a under scope b#c and transition a#b under scope c both mint a#b#c:0"]
theorem nu011_collision :
    mintName "a" "b#c" 0 = "a#b#c:0" ∧ mintName "a#b" "c" 0 = "a#b#c:0" := by
  decide

/-- AC6's parse example: transition `x#y:z`, whose own name holds `#` and `:`, mints
`x#y:z#s:4` under scope `s` with counter 4, and any accepted scope, transition and counter that
mint the same name are `s`, `x#y:z` and 4. -/
@[evidence cites "NU-011" "AC6: a name minted by a transition whose own name contains # and : splits back into transition, scope and counter by the rule above"]
theorem nu011_ac6 :
    mintName "x#y:z" "s" 4 = "x#y:z#s:4" ∧
      ∀ {t s : String} {n : Nat}, refValidScope s = true →
        mintName t s n = "x#y:z#s:4" → t = "x#y:z" ∧ s = "s" ∧ n = 4 := by
  refine ⟨by decide, fun hs h => ?_⟩
  have h' : mintName _ _ _ = mintName "x#y:z" "s" 4 := h.trans (by decide)
  exact nu011_parse hs (by decide) h'

/-- A scope of 32 lowercase hexadecimal characters is an accepted scope. -/
theorem nu011_default_accepted (s : String) (hlen : s.length = 32)
    (hhex : ∀ c ∈ s.toList, c ∈ nu011_hexDigits) : refValidScope s = true := by
  rw [refValidScope_iff]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · subst h
    simp at hlen
  · have := hhex _ h
    revert this
    decide
  · have := hhex _ h
    revert this
    decide

/-- A default scope drawn under the default block is an accepted scope, so the format and
lineage blocks cover the names minted under it. -/
@[evidence cites "NU-011" "AC5: an executor given no scope mints names whose scope component is 32 lowercase hexadecimal characters"]
theorem nu011_default_draw_accepted {D : Nat → String → Prop} (h : NU_011_default D) {k : Nat}
    {s : String} (hd : D k s) : refValidScope s = true :=
  nu011_default_accepted s (h k s hd).1 (h k s hd).2

/-- **The default is not the run identifier.** Whatever run identifier `rid k` the `k`-th
executor of a process publishes, a draw that is not fixed can differ from it. -/
@[evidence cites "NU-011" "The run identifier remains the reproducible one, the default scope is the unique one, and an implementation MUST NOT derive either from the other"]
theorem nu011_default_not_runId {D : Nat → String → Prop} (h : DefaultUnfixed D)
    (rid : Nat → String) (k : Nat) : ∃ s, D k s ∧ s ≠ rid k :=
  h k (rid k)

/-- **AC2.** A join correlates two tokens only when their names are equal. Take a name `n` that
an earlier segment minted under scope `s`, and a name `x` that the resumed segment mints under
another accepted scope `s'`: no join correlates `n` with `x`, because the two names differ. -/
@[evidence cites "NU-011" "AC2: a restored token awaiting its sibling at a NU-020 join is not correlated with a freshly minted token of the resumed segment"]
theorem nu011_ac2 {Sy : MintSys} {V : ScopeCheck} (h : NU_011_format Sy V) {s s' : String}
    (hs : V s = true) (hs' : V s' = true) (hne : s ≠ s') {evs evs' : List MintEv}
    {xs xs' : List String} (hr : MintRun Sy (Sy.init s) evs xs)
    (hr' : MintRun Sy (Sy.init s') evs' xs') (corr : String → String → Prop)
    (hcorr : ∀ a b, corr a b → a = b) : ∀ n ∈ xs, ∀ x ∈ xs', ¬ corr n x := by
  intro n hn x hx hc
  exact nu011_lineage_of_format h s s' hs hs' hne evs evs' xs xs' hr hr' n hn
    (hcorr n x hc ▸ hx)

/-- **What the host assumption buys.** Take two executions of one lineage under pinned, accepted
scopes, listed for the host block. If they share a minted name, they run the same segment and
mint the same names: the only names two executions share are the ones a replay reproduces. -/
@[evidence cites "NU-011" "AC3 and the replay exception: two executions of one lineage share a minted name only when one replays the other"]
theorem nu011_host_replay {Sy : MintSys} {V : ScopeCheck} (hf : NU_011_format Sy V)
    {es : List (String × Nat × List String)} (hh : NU_011_host es)
    {e e' : String × Nat × List String} (he : e ∈ es) (he' : e' ∈ es)
    (hv : V e.1 = true) (hv' : V e'.1 = true) {evs evs' : List MintEv} {xs xs' : List String}
    (hc : calls evs = e.2.2) (hc' : calls evs' = e'.2.2)
    (hr : MintRun Sy (Sy.init e.1) evs xs) (hr' : MintRun Sy (Sy.init e'.1) evs' xs')
    {x : String} (hx : x ∈ xs) (hx' : x ∈ xs') : e.2.1 = e'.2.1 ∧ xs = xs' := by
  have hs : e.1 = e'.1 := by
    refine Classical.byContradiction fun hne => ?_
    exact nu011_lineage_of_format hf e.1 e'.1 hv hv' hne evs evs' xs xs' hr hr' x hx hx'
  have h2 := hh e he e' he' hs
  refine ⟨congrArg Prod.fst h2, ?_⟩
  rw [hf.2.2 _ hv evs xs hr, hf.2.2 _ hv' evs' xs' hr', hc, hc', hs, h2]

/-- Without a replay, the host block makes the pinned scopes pairwise distinct: if no two
executions run the same segment, no two share a scope. -/
theorem nu011_host_distinct {es : List (String × Nat × List String)} (hh : NU_011_host es)
    (hseg : (es.map fun e => e.2.1).Nodup) : (es.map Prod.fst).Nodup := by
  induction es with
  | nil => exact List.nodup_nil
  | cons e es ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hseg ⊢
    refine ⟨fun ⟨e', he', hs⟩ => hseg.1 ⟨e', he', ?_⟩,
      ih (fun a ha b hb => hh a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        hseg.2⟩
    exact congrArg Prod.fst (hh e' (List.mem_cons_of_mem _ he') e List.mem_cons_self hs)

/-- **Every name of a lineage once.** Take the executions of one restore lineage, each a scope
and the names it minted. If every scope is accepted and no two are equal (for pinned scopes by
the host block without a replay, `nu011_host_distinct`; for default ones by the random draw), the
minter meets the lineage block and mints distinct names within one execution (NU-010), then
every name minted in the lineage is minted once. -/
@[evidence cites "NU-011" "AC4: two concurrent executions restored from the same snapshot, under the default scope or under two different pinned scopes, mint disjoint name sets"]
theorem nu011_lineage_nodup {Sy : MintSys} {V : ScopeCheck} (hl : NU_011_lineage Sy V)
    (hu : ∀ s evs xs, MintRun Sy (Sy.init s) evs xs → xs.Nodup) :
    ∀ rs : List (String × List String),
      (∀ r ∈ rs, V r.1 = true ∧ ∃ evs, MintRun Sy (Sy.init r.1) evs r.2) →
      (rs.map Prod.fst).Nodup → (rs.map Prod.snd).flatten.Nodup
  | [], _, _ => List.nodup_nil
  | r :: rs, hr, hh => by
    simp only [List.map_cons, List.nodup_cons] at hh
    simp only [List.map_cons, List.flatten_cons, List.nodup_append]
    obtain ⟨hv, evs, hrun⟩ := hr r List.mem_cons_self
    refine ⟨hu _ _ _ hrun,
      nu011_lineage_nodup hl hu rs (fun r' hm => hr r' (List.mem_cons_of_mem _ hm)) hh.2,
      fun x hx y hy hxy => ?_⟩
    subst hxy
    obtain ⟨l, hl', hxl⟩ := List.mem_flatten.1 hy
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hl'
    obtain ⟨hv', evs', hrun'⟩ := hr r' (List.mem_cons_of_mem _ hr')
    have hne : r.1 ≠ r'.1 := fun he => hh.1 (he ▸ List.mem_map_of_mem hr')
    exact hl r.1 r'.1 hv hv' hne evs evs' r.2 r'.2 hrun hrun' x hx hxl

/-- The reference instance: with pairwise distinct accepted scopes, the reference minter mints
every name of a lineage once. -/
theorem nu011_ref_lineage_nodup (rs : List (String × List String))
    (hr : ∀ r ∈ rs, refValidScope r.1 = true ∧
      ∃ evs, MintRun refMintSys (refMintSys.init r.1) evs r.2)
    (hh : (rs.map Prod.fst).Nodup) : (rs.map Prod.snd).flatten.Nodup :=
  nu011_lineage_nodup NU_011_lineage_reference (fun _ _ _ h => refRun_nodup h) rs hr hh

/-- The host assumption is load-bearing: segment 0 runs under the pinned scope `s` and fires
`fork` once, minting `fork#s:0`; the execution that resumes its marking, segment 1, is pinned to
`s` again and fires `fork` once, minting `fork#s:0` a second time. That lineage breaks the host
block. -/
theorem nu011_host_needed :
    MintRun refMintSys (refMintSys.init "s") [.call "fork"] ["fork#s:0"] ∧
      ¬ (["fork#s:0"] ++ ["fork#s:0"]).Nodup ∧
      ¬ NU_011_host [("s", 0, ["fork"]), ("s", 1, ["fork"])] :=
  ⟨refRun_iff.2 (by decide), by decide, by unfold NU_011_host; decide⟩

/-! ## Nonvacuity and the acceptance criteria -/

/-- ✓ Worked example (AC6, the n-th name). The reference check accepts the blank scope `" "` and
the scope `s`, and refuses `""`, `a:b` and `a#b`. Under scope `s`, the calls `fork`, then a
firing boundary, then `fork` and `split` return `fork#s:0`, `fork#s:1` and `split#s:2`: one
counter for the executor, not reset at the boundary, not kept per transition. -/
@[evidence nonvacuous NU_011_format]
theorem NU_011_format_nonvacuous :
    refValidScope " " = true ∧ refValidScope "s" = true ∧ refValidScope "" = false ∧
      refValidScope "a:b" = false ∧ refValidScope "a#b" = false ∧
      MintRun refMintSys (refMintSys.init "s")
        [.call "fork", .boundary, .call "fork", .call "split"]
        ["fork#s:0", "fork#s:1", "split#s:2"] :=
  ⟨by decide, by decide, by decide, by decide, by decide, refRun_iff.2 (by decide)⟩

/-- ✓ Worked example (AC1, AC4). A prior execution under scope `a` minted `fork#a:0` into the
marking it left. The execution restored from it runs under scope `b` and fires `fork` twice,
minting `fork#b:0` and `fork#b:1`; neither is `fork#a:0`. A second execution restored from the
same snapshot under scope `c` mints `fork#c:0` and `fork#c:1`, none shared with `b`'s. -/
@[evidence nonvacuous NU_011_lineage]
theorem NU_011_lineage_nonvacuous :
    MintRun refMintSys (refMintSys.init "a") [.call "fork"] ["fork#a:0"] ∧
      MintRun refMintSys (refMintSys.init "b") [.call "fork", .boundary, .call "fork"]
        ["fork#b:0", "fork#b:1"] ∧
      MintRun refMintSys (refMintSys.init "c") [.call "fork", .boundary, .call "fork"]
        ["fork#c:0", "fork#c:1"] ∧
      "fork#a:0" ∉ ["fork#b:0", "fork#b:1"] ∧
      (∀ x ∈ ["fork#b:0", "fork#b:1"], x ∉ ["fork#c:0", "fork#c:1"]) :=
  ⟨refRun_iff.2 (by decide), refRun_iff.2 (by decide), refRun_iff.2 (by decide), by decide,
    by decide⟩

/-- ✓ Worked example (AC5). An executor given no scope may draw
`0123456789abcdef0123456789abcdef` or `fedcba9876543210fedcba9876543210`, two different scopes,
and both are accepted scopes; it never draws the dashed form
`00000000-0000-4000-8000-000000000000`. -/
@[evidence nonvacuous NU_011_default]
theorem NU_011_default_nonvacuous :
    refDefaultDraw 0 "0123456789abcdef0123456789abcdef" ∧
      refDefaultDraw 0 "fedcba9876543210fedcba9876543210" ∧
      "0123456789abcdef0123456789abcdef" ≠ "fedcba9876543210fedcba9876543210" ∧
      refValidScope "0123456789abcdef0123456789abcdef" = true ∧
      ¬ refDefaultDraw 0 "00000000-0000-4000-8000-000000000000" := by
  unfold refDefaultDraw nu011_hexDigits
  decide

/-- ✓ Worked example (AC3, the replay). Segment 0 runs under the pinned scope `s1` and fires
`fork` once; segment 1 resumes it under `s2`; a later replay of segment 0 runs under `s1` again
with the same call. The host block holds, segment 0 and its replay both mint `fork#s1:0`, and
segment 1 mints `fork#s2:0`, a name of its own. -/
@[evidence nonvacuous NU_011_host]
theorem NU_011_host_nonvacuous :
    NU_011_host [("s1", 0, ["fork"]), ("s2", 1, ["fork"]), ("s1", 0, ["fork"])] ∧
      MintRun refMintSys (refMintSys.init "s1") [.call "fork"] ["fork#s1:0"] ∧
      MintRun refMintSys (refMintSys.init "s2") [.call "fork"] ["fork#s2:0"] ∧
      (["fork#s1:0"] ++ ["fork#s2:0"]).Nodup :=
  ⟨by unfold NU_011_host; decide, refRun_iff.2 (by decide), refRun_iff.2 (by decide), by decide⟩

/-! ## Forbidden models -/

/-- A scope check that bans `:` but not `#`. -/
def nu011_hashOk : ScopeCheck := fun s => decide (s ≠ "") && decide (':' ∉ s.toList)

/-- A scope check that bans `#` but not `:`. -/
def nu011_colonOk : ScopeCheck := fun s => decide (s ≠ "") && decide ('#' ∉ s.toList)

/-- A scope check that tests for blankness instead of length zero. -/
def nu011_blankTest : ScopeCheck := fun s =>
  decide (s.toList.any (fun c => !c.isWhitespace) = true) && decide (':' ∉ s.toList) &&
    decide ('#' ∉ s.toList)

/-- A minter whose counter is not a counter: a call may return any number. -/
def nu011_randomCounter : MintSys where
  St := MintSt
  init s := ⟨s, 0⟩
  mint st t x st' := ∃ n, x = mintName t st.scope n ∧ st' = { st with ctr := st.ctr + 1 }
  next := id

/-- A minter that mixes a salt (here the fixed text `-r`) into the pinned scope. -/
def nu011_salted : MintSys where
  St := MintSt
  init s := ⟨s ++ "-r", 0⟩
  mint st t x st' := x = (refMint st t).1 ∧ st' = (refMint st t).2
  next := id

/-- A minter with one counter per transition: the state is the scope and a counter for every
transition name. -/
def nu011_perTrans : MintSys where
  St := String × (String → Nat)
  init s := (s, fun _ => 0)
  mint st t x st' := x = mintName t st.1 (st.2 t) ∧
    st' = (st.1, fun u => if u = t then st.2 t + 1 else st.2 u)
  next := id

/-- A minter whose counter starts again from zero at every firing boundary. -/
def nu011_perFiring : MintSys where
  St := MintSt
  init s := ⟨s, 0⟩
  mint st t x st' := x = (refMint st t).1 ∧ st' = (refMint st t).2
  next st := { st with ctr := 0 }

/-- A minter that ignores the host's scope and uses one scope for its process, here `p`. -/
def nu011_perProcess : MintSys where
  St := MintSt
  init _ := ⟨"p", 0⟩
  mint st t x st' := x = (refMint st t).1 ∧ st' = (refMint st t).2
  next := id

/-- ✗ A check that bans `:` but not `#` accepts `a#b`, breaking the first line. -/
@[evidence forbids NU_011_format]
theorem NU_011_format_forbids_hashOk : ¬ NU_011_format refMintSys nu011_hashOk := by
  intro h
  have := h.1 "a#b" (Or.inr (Or.inr (by decide)))
  revert this
  decide

/-- ✗ A check that bans `#` but not `:` accepts `a:b`, breaking the first line. Every minted name
still parses (the counter digits hold no `:`), so only the validation line catches it. -/
@[evidence forbids NU_011_format]
theorem NU_011_format_forbids_colonOk : ¬ NU_011_format refMintSys nu011_colonOk := by
  intro h
  have := h.1 "a:b" (Or.inr (Or.inl (by decide)))
  revert this
  decide

/-- ✗ A check that refuses a blank scope rejects `" "`, which is not empty and holds no
separator, breaking the second line. -/
@[evidence forbids NU_011_format]
theorem NU_011_format_forbids_blankTest : ¬ NU_011_format refMintSys nu011_blankTest := by
  intro h
  have := h.2.1 " " (by decide) (by decide) (by decide)
  revert this
  decide

/-- ✗ A minter that may return any counter: under scope `s`, the first call by `t` returns
`t#s:7` instead of `t#s:0`, breaking the last line. -/
@[evidence forbids NU_011_format]
theorem NU_011_format_forbids_randomCounter :
    ¬ NU_011_format nu011_randomCounter refValidScope := by
  intro h
  have := h.2.2 "s" (by decide) [.call "t"] ["t#s:7"]
    (.call ⟨7, by decide, rfl⟩ (.nil _))
  revert this
  decide

/-- ✗ A minter that mixes a salt into the pinned scope `s` returns `t#s-r:0` for the first call,
not `t#s:0`, breaking the last line. -/
@[evidence forbids NU_011_format]
theorem NU_011_format_forbids_salted : ¬ NU_011_format nu011_salted refValidScope := by
  intro h
  have := h.2.2 "s" (by decide) [.call "t"] ["t#s-r:0"]
    (.call (s' := (refMint ⟨"s" ++ "-r", 0⟩ "t").2) ⟨by decide, rfl⟩ (.nil _))
  revert this
  decide

/-- ✗ A minter with one counter per transition: under scope `s`, `fork` then `split` mint
`fork#s:0` and `split#s:0`, where one counter for the executor gives `split#s:1`. The names are
still distinct and still carry the scope; only the last line catches it. -/
@[evidence forbids NU_011_format]
theorem NU_011_format_forbids_perTrans : ¬ NU_011_format nu011_perTrans refValidScope := by
  intro h
  have := h.2.2 "s" (by decide) [.call "fork", .call "split"] ["fork#s:0", "split#s:0"]
    (.call ⟨by decide, rfl⟩ (.call ⟨by decide, rfl⟩ (.nil _)))
  revert this
  decide

/-- ✗ A minter that counts each firing from zero: under scope `s`, `fork`, a firing boundary, then
`fork` again mint `fork#s:0` twice, where counting across firings gives `fork#s:1` for the second
call. This breaks the last line. -/
@[evidence forbids NU_011_format]
theorem NU_011_format_forbids_perFiring : ¬ NU_011_format nu011_perFiring refValidScope := by
  intro h
  have := h.2.2 "s" (by decide) [.call "fork", .boundary, .call "fork"] ["fork#s:0", "fork#s:0"]
    (.call (s' := (refMint ⟨"s", 0⟩ "fork").2) ⟨by decide, rfl⟩
      (.boundary (.call (s' := (refMint ⟨"s", 0⟩ "fork").2) ⟨by decide, by decide⟩ (.nil _))))
  revert this
  decide

/-- ✗ With a check that accepts `#`, transition `a` under scope `b#c` and transition `a#b` under
scope `c` both mint `a#b#c:0`: two different accepted scopes, one name. -/
@[evidence forbids NU_011_lineage]
theorem NU_011_lineage_forbids_hashOk : ¬ NU_011_lineage refMintSys nu011_hashOk := by
  intro h
  exact h "b#c" "c" (by decide) (by decide) (by decide) [.call "a"] [.call "a#b"]
    ["a#b#c:0"] ["a#b#c:0"] (refRun_iff.2 (by decide)) (refRun_iff.2 (by decide))
    "a#b#c:0" (by decide) (by decide)

/-- ✗ A minter that uses one scope per process: an execution under scope `a` and one under scope
`b`, each firing `t` once, both mint `t#p:0`. This is the silent merge the body describes when
the first executor of a new process resumes a marking. -/
@[evidence forbids NU_011_lineage]
theorem NU_011_lineage_forbids_perProcess : ¬ NU_011_lineage nu011_perProcess refValidScope := by
  intro h
  have hr : ∀ s, MintRun nu011_perProcess (nu011_perProcess.init s) [.call "t"] ["t#p:0"] :=
    fun _ => .call (s' := (refMint ⟨"p", 0⟩ "t").2)
      ⟨(by decide : "t#p:0" = (refMint ⟨"p", 0⟩ "t").1), rfl⟩ (.nil _)
  exact h "a" "b" (by decide) (by decide) (by decide) _ _ _ _ (hr "a") (hr "b")
    "t#p:0" (by decide) (by decide)

/-- The execution id `k` written in 32 hexadecimal digits, padded with zeros. -/
def nu011_hexId (k : Nat) : String :=
  String.ofList (List.replicate (32 - (Nat.toDigits 16 k).length) '0' ++ Nat.toDigits 16 k)

/-- A default draw derived from the run identifier: the `k`-th executor of a process always runs
under its execution id `k` in 32 hexadecimal digits. -/
def nu011_fromId : Nat → String → Prop := fun k s => s = nu011_hexId k

/-- A default draw written as a UUID with its dashes kept. -/
def nu011_dashedDraw : Nat → String → Prop := fun _ s =>
  s = "00000000-0000-4000-8000-000000000000" ∨ s = "00000000-0000-4000-8000-000000000001"

/-- A default derived from the execution id: the first executor of every process runs under
`000…0`, so no other draw is possible for it, and the coverage conjunct `DefaultUnfixed` fails. -/
@[evidence cites "NU-011" "AC5: the default scope is not the run identifier; a default derived from the execution id is fixed by the construction order, which the coverage conjunct DefaultUnfixed of joint_nu_sketch rules out"]
theorem nu011_fromId_fixed : ¬ DefaultUnfixed nu011_fromId := by
  intro h
  obtain ⟨s', hs', hne⟩ := h 0 (nu011_hexId 0)
  exact hne hs'

/-- ✗ A default written with the dashes of a UUID is 36 characters long and holds `-`,
breaking the line. -/
@[evidence forbids NU_011_default]
theorem NU_011_default_forbids_dashed : ¬ NU_011_default nu011_dashedDraw := by
  intro h
  have := (h 0 _ (Or.inl rfl)).1
  revert this
  decide

/-- The silent merge the id-derived default causes, although its scope is an accepted one: the
process that persisted a snapshot and the process that resumes it each build their first
executor with no scope, both run under `00000000000000000000000000000000`, and both mint
`fork#00000000000000000000000000000000:0` for their first `fork`. -/
theorem nu011_fromId_merge :
    nu011_hexId 0 = "00000000000000000000000000000000" ∧
      refValidScope (nu011_hexId 0) = true ∧
      MintRun refMintSys (refMintSys.init (nu011_hexId 0)) [.call "fork"]
        ["fork#00000000000000000000000000000000:0"] := by
  have h0 : nu011_hexId 0 = "00000000000000000000000000000000" := by decide
  refine ⟨h0, ?_, ?_⟩
  · rw [h0]; decide
  · rw [h0]; exact refRun_iff.2 (by decide)

/-- ✗ A host that pins scope `s` for segment 0 and again for segment 1, the execution resuming
it, breaks the host block. -/
@[evidence forbids NU_011_host]
theorem NU_011_host_forbids_sameScope : ¬ NU_011_host [("s", 0, ["fork"]), ("s", 1, ["fork"])] := by
  unfold NU_011_host
  decide

/-- ✗ A replay that makes other calls than the segment it re-runs: segment 0 under `s` calls
`fork` twice and mints `fork#s:0` and `fork#s:1`; the replay under `s` calls `split`, then
`fork`, and mints `split#s:0` and `fork#s:1`, the segment's second name, for another token. The
replay exception does not cover it. -/
@[evidence forbids NU_011_host]
theorem NU_011_host_forbids_divergentReplay :
    ¬ NU_011_host [("s", 0, ["fork", "fork"]), ("s", 0, ["split", "fork"])] := by
  unfold NU_011_host
  decide

/-! ## The coverage conjunct -/

/-- A minter that refuses a `freshName()` call by a transition whose own name holds `:` or `#`
(the slip of running the scope check on the transition name as well). -/
def nu011_noSepTrans : MintSys where
  St := MintSt
  init s := ⟨s, 0⟩
  mint st t x st' := ':' ∉ t.toList ∧ '#' ∉ t.toList ∧
    x = (refMint st t).1 ∧ st' = (refMint st t).2
  next := id

/-- Every run of the refusing minter is a reference run. -/
theorem nu011_noSepTrans_sub {st : nu011_noSepTrans.St} {evs : List MintEv}
    {xs : List String} (h : MintRun nu011_noSepTrans st evs xs) :
    MintRun refMintSys (st : MintSt) evs xs := by
  induction h with
  | nil s => exact MintRun.nil (Sy := refMintSys) s
  | call hm _ ih => exact .call ⟨hm.2.2.1, hm.2.2.2⟩ ih
  | boundary _ ih => exact .boundary ih

/-- **Why the coverage conjunct is needed.** A minter that answers no call by AC6's transition
`x#y:z` meets the format and lineage blocks, because every line speaks of runs that exist; the
coverage conjunct `MintTotal` (every call is answered), which the reference meets, rejects it. -/
theorem nu011_noSepTrans_needs_cover :
    NU_011_format nu011_noSepTrans refValidScope ∧
      NU_011_lineage nu011_noSepTrans refValidScope ∧
      ¬ MintTotal nu011_noSepTrans ∧ MintTotal refMintSys := by
  refine ⟨⟨NU_011_format_reference.1, NU_011_format_reference.2.1,
      fun s hs evs xs h => NU_011_format_reference.2.2 s hs evs xs (nu011_noSepTrans_sub h)⟩,
    fun s s' hs hs' hne evs evs' xs xs' h h' =>
      NU_011_lineage_reference s s' hs hs' hne evs evs' xs xs'
        (nu011_noSepTrans_sub h) (nu011_noSepTrans_sub h'),
    fun h => ?_, refMintSys_total⟩
  obtain ⟨x, st', hm⟩ := h ⟨"s", 0⟩ "x#y:z"
  exact hm.1 (by decide)

end Libpetri.Spec
