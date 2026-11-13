import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Spec.Req.CORE_040
import Libpetri.Spec.Req.EXEC_042
import Libpetri.Spec.Text.MOD_006

set_option linter.missingDocs true

/-!
# MOD-006: Subnet validation at build (`spec/11-modular-composition.md`)

MOD-006 is a behaviour requirement (kind B) over two abstract functions: the net builder `NB`
that builds a subnet's body (a `NetBuilder` over `defsTB`, whose instances are the body's
transition definitions, so CORE-040 and EXEC-042's build block apply to the very same `NB`) and
the subnet builder `SB : SubnetMake N A`, which turns what the host declared (`SubnetIn`: a
name, declared places, transition definitions, declared terminal places, ports and channels)
into a subnet definition or a rejection with a message.

The block says when building a subnet fails: a port on a place the built body does not hold, a
channel on a transition name the built body does not hold, two ports of one name, two channels
of one name, a body the net builder rejects. It says that building succeeds otherwise, and that
the message of a failure contains the body's own rejection message, the name of a port or channel
whose name another one carries, or (when the body builds) the name of a port or channel that the
built body does not hold. Which offender is named when there are several is not stated, nor the
order of the checks.

The witness is the reference subnet builder `refSubnetBuild NB`, which does what Rust, Java and
TypeScript do: build the body first, then walk the ports (duplicate name, then place), then the
channels (duplicate name, then transition). The block holds of it for every net builder `NB`, and
also of a builder that checks the names before it builds the body (`MOD_006_allows_namesFirst`).
Jointly with CORE-040 the "body" of lines 1 and 6 is the collected net: a port on a place that
only an arc names is accepted, and a port on a place nobody declared or named fails
(`mod006_core040`). Jointly with EXEC-042's build block, a declared terminal place that no body
transition consumes from or reads is no reason to reject (`mod006_exec042`). Wrong builders are
killed, one per load-bearing line.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The subnet builder's types -/

section Types

variable (N A : Type)

/-- The transition builder whose instances are a subnet body's transition definitions. A subnet
builder receives transitions that were already built ([CORE-020]); this builder only types the
body for the net builder, so that the net builder of a subnet body is a `NetBuilder` in the sense
of [CORE-040] and [EXEC-042]. Two instances are the same transition when their names are equal
(rulings D10, D23). -/
def defsTB : TBuilder N A where
  I := CDef N A
  build _ i := .ok { toTransDef := i.resolve }
  defOf d := d.toTransDef
  same x y := x.core.name = y.core.name

/-- A subnet builder ([MOD-006]): what the host declared gives a subnet definition or a rejection
with a message (a panic or an exception, read as `.error msg`). -/
abbrev SubnetMake := SubnetIn N A → Except String (SubnetDef N A)

end Types

variable {N A : Type}

/-- The body of a subnet input as its net builder sees it: the declared places, the transition
definitions in the order added, and the declared terminal places. -/
def SubnetIn.body (S : SubnetIn N A) : NetIn (defsTB N A) :=
  { places := S.places, trans := S.defs, terminals := S.terminals }

/-! ## MOD-006: Subnet Validation at Build -/

requirement MOD_006
  id "MOD-006"
  title "Subnet Validation at Build"
  kind B
  scope "every subnet builder"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_006.s1, MOD_006.s2, MOD_006.s3, MOD_006.s4, MOD_006.s5, MOD_006.s6, MOD_006.s7
  reading "For every net builder NB of subnet bodies and every subnet builder SB:"
          "if NB builds the body of S as the net b and some port of S exposes a place that is not a place of b, SB fails on S;"
          "if NB builds the body of S as b and some channel of S names a transition that is not the name of a transition of b, SB fails on S;"
          "if two ports of S have the same name, SB fails on S;"
          "if two channels of S have the same name, SB fails on S;"
          "if NB rejects the body of S, SB fails on S;"
          "if NB builds the body of S as b, every port exposes a place of b, every channel names a transition of b, and the port names and the channel names are each pairwise distinct, SB succeeds on S;"
          "if SB fails on S with the message msg, then NB rejects the body with a message e that msg contains, or msg contains the name of a port whose name two ports carry or of a channel whose name two channels carry, or NB builds the body as b and msg contains the name of a port whose place is not in b or of a channel whose transition is not the name of a transition of b."
  assumes "A subnet builder (SubnetMake) is the build call of one implementation's subnet-definition builder, read as a function from what the host declared (SubnetIn: the definition's name, the declared places, the transition definitions in the order added, the declared terminal places, the ports and the channels) to a subnet definition or a rejection with a message (a panic or an exception, read as .error msg). The body net builder NB is a parameter: every runtime builds the body with its net builder first and checks the interface against the built net (SubnetDefBuilder::build in rust/libpetri-core/src/subnet_def.rs, SubnetDef.Builder.build in java/src/main/java/org/libpetri/core/SubnetDef.java, SubnetDefBuilder.build in typescript/src/core/subnet-def.ts). NB is typed as a CORE-040 net builder over defsTB (instances are the body's definitions), so CORE-040, EXEC-042's build block and this block speak of the same function; the holds theorem holds for every NB."
          "Line 1 and line 6 compare a port's place with the places of the built body by equality on the place type N (CORE-002: by name in TypeScript, Rust and Python, by name and token type in Java, the port-place check of SubnetDefBuilder::build in rust/libpetri-core/src/subnet_def.rs, SubnetDef.Builder.build in java/src/main/java/org/libpetri/core/SubnetDef.java, SubnetDefBuilder.build in typescript/src/core/subnet-def.ts). The built body holds the declared places and every place an arc of a body transition names (CORE-040 line 2 and line 3), so under any net builder that meets CORE-040 a port on a place that only an arc names is accepted and a port on a place nobody declared or named fails (mod006_core040)."
          "Line 2 and line 6 match a channel to a body transition by name (ruling D23, settled by D10, and the R-MA3 (a) reading of the mod-a map): the model's channel carries the transition's name, so line 6's 'every channel exposes a transition of the built body' reads as 'the name of every channel's transition is the name of a transition of the built body'. Rust and Python store and compare names (the transition_name field of Channel in rust/libpetri-core/src/interface.rs, the channel check of SubnetDefBuilder::build in rust/libpetri-core/src/subnet_def.rs); Java and TypeScript compare transition objects (the channel check of SubnetDef.Builder.build in java/src/main/java/org/libpetri/core/SubnetDef.java and of SubnetDefBuilder.build in typescript/src/core/subnet-def.ts), so a channel over a second transition object that has the name of a body transition is rejected there and accepted in Rust. Under the shared unique-names assumption (D10, D23; no builder checks names) two transitions of one name are one transition, and that case is outside the block. The markdown calls it implementation-defined and keeps line 6 on transitions, not names, so that the English line does not decide it: a channel whose transition's name is no body transition's name fails everywhere (line 2), a channel over a body transition builds everywhere (line 6). The markdown cites TIME-010 for the unique-names assumption, where ruling D10 put it (spec/03-timing.md)."
          "Lines 3, 4 and 6 treat port names and channel names as two namespaces, as all three runtimes do: a port and a channel may share a name, and line 6 then asks the build to succeed. MOD-005 item 1 leaves a shared namespace implementation-defined; MOD-006's markdown fixes the two namespaces for subnet definitions ('Port names and channel names are two namespaces'), so an implementation with one shared namespace violates line 6. Java refuses a blank port or channel name when the port or channel value is constructed (the compact constructors of the Interface.Port records and of Interface.Channel.SyncChannel call requireNonBlank, java/src/main/java/org/libpetri/core/Interface.java), before any subnet builder sees it, so line 6 speaks of the ports and channels Java can construct; TypeScript and Rust accept a blank name. On the interface-builder route of MOD-014 (fromNet) a duplicate name is rejected even earlier, at the port() or channel() call (InterfaceBuilder::port in rust/libpetri-core/src/interface.rs, Interface.Builder.port in java/src/main/java/org/libpetri/core/Interface.java, InterfaceBuilder.port in typescript/src/core/interface.ts), which meets AC1's 'not later'."
          "Line 5 is item 5 as reworded under rulings D20 and R-MA7 (3): a body the net builder rejects yields no subnet definition. The CORE-041 reference of the old item is dropped (CORE-041 is immutability and names no check). Through the subnet builders of the runtimes the case cannot arise: they take places, transitions, ports and channels only, transition checks run when a transition is built (CORE-020), and without composition and fusion the net builder rejects only a terminal place that a transition consumes from or reads (EXEC-042 AC5), which no subnet builder can declare. The model's input carries terminal places (for fromNet, MOD-014), so under the reference net builder the line has an instance: a body whose terminal place a transition consumes from (MOD_006_nonvacuous). A body that declares a terminal place and no such clash builds under every net builder that meets EXEC-042's build block, and then line 6 asks the subnet build to succeed when the interface is fine (mod006_exec042; MOD_006_nonvacuous builds buf with the terminal place done); instantiate and composition refuse such a body (EXEC-042 AC6; MOD-010 line 4, MOD-025 line 7)."
          "Line 6 is implied by line 7 (mod006_line6_of_line7): when the body builds and no port or channel offends, line 7 leaves no message a failure could carry, so the build succeeds. Line 6 is kept as the acceptance line the composition design asks of every partial builder (skeptic correction S2) and has no mutant of its own (as for MOD-010 AC2, skeptic correction S4)."
          "Line 7 is AC2 and the sentence 'Each failure MUST produce an error identifying the offending element by name.': to name an element is for the message to contain its name as a substring (List.IsInfix on the characters). A duplicate port or channel name (cases 3 and 4) does not depend on the body, so a message naming it meets the line whether or not the net builder builds the body, and a builder may check the names before it builds the body (MOD_006_allows_namesFirst; the markdown's 'may be checked before the body is built'); a port or channel offends against case 1 or 2 only when the body builds. The three runtimes build the body first. The line is existential over the offenders: the runtimes walk the ports in declaration order (duplicate name, then place), then the channels (SubnetDefBuilder::build in rust/libpetri-core/src/subnet_def.rs, SubnetDef.Builder.build in java/src/main/java/org/libpetri/core/SubnetDef.java, SubnetDefBuilder.build in typescript/src/core/subnet-def.ts), and Rust's from_net walks a hash set, so which offender is named when there are several is not stated. All three runtimes name the port or channel and also its place or transition; the line asks for the port or channel only. A body rejection passes the net builder's message through unchanged in all three (a panic or exception from the body build); the line allows a message that wraps it."
          "Naming by substring is weaker than 'identifying', taken as the modelling choice. A message names every port or channel whose name it happens to contain: the message 'Subnet buf is invalid' names a port called in or a. A port or channel with a blank name, which TypeScript and Rust accept, is named by every message, so line 7 asks nothing of a failure that such a port or channel offends. A message that lists the name of every port and channel meets the line, so the line does not rule out a message that names innocent ports or channels next to the offender (open item: a clause that the message names no port or channel that does not offend is hard to state soundly, because one name can be a substring of another, as in is of input)."
          "For case 5 line 7 asks only that the message contain the net builder's message. That this message names the offending place or transition is the net builder's matter (CORE-040, EXEC-042), not this block's: when the net builder rejects with a message that names nothing, or with the empty message, line 7 asks nothing more of the subnet builder. For cases 1 to 4 the line asks for the port or channel's name, which is one reading of AC2's 'the offending port, channel, place, or transition'."
          "AC1(each rejection case produces an error at subnet build, not later at instantiation or composition) is lines 1 to 5: they are stated of the subnet builder itself. A builder that accepts everything and leaves the checks to instantiation violates line 1 (MOD_006_forbids_lazy). AC2 (error messages name the offending port, channel, place or transition) is line 7. AC3 (a valid subnet definition is immutable after build) is a quality property of the host values (Lean values are immutable; builder stability is CORE-041's line), tested and not proven. What a built definition holds (its ports, channels and body) is MOD-001's line. The test derivation covers rejection cases 1 to 4; case 5 has no runtime input, since the subnet-definition builder takes places, transitions, ports and channels only and fromNet (MOD-014) takes a net that is already built (above)."
  signoff "2026-11-13 87a8b78435a46624 ai"
  statement : ∀ {N A : Type}, NetBuilder (defsTB N A) → SubnetMake N A → Prop :=
    fun {N A} NB SB =>
      (∀ (S : SubnetIn N A) b, NB S.body = .ok b →
        ∀ q ∈ S.ports, q.place ∉ b.places → ∃ msg, SB S = .error msg) ∧
      (∀ (S : SubnetIn N A) b, NB S.body = .ok b →
        ∀ c ∈ S.chans, c.trans ∉ b.trans.map (·.core.name) → ∃ msg, SB S = .error msg) ∧
      (∀ S : SubnetIn N A, ¬ (S.ports.map (·.name)).Nodup → ∃ msg, SB S = .error msg) ∧
      (∀ S : SubnetIn N A, ¬ (S.chans.map (·.name)).Nodup → ∃ msg, SB S = .error msg) ∧
      (∀ (S : SubnetIn N A) e, NB S.body = .error e → ∃ msg, SB S = .error msg) ∧
      (∀ (S : SubnetIn N A) b, NB S.body = .ok b →
        (∀ q ∈ S.ports, q.place ∈ b.places) →
        (∀ c ∈ S.chans, c.trans ∈ b.trans.map (·.core.name)) →
        (S.ports.map (·.name)).Nodup → (S.chans.map (·.name)).Nodup → ∃ D, SB S = .ok D) ∧
      (∀ (S : SubnetIn N A) msg, SB S = .error msg →
        (∃ e, NB S.body = .error e ∧ MsgNames msg e) ∨
        (∃ q ∈ S.ports, 2 ≤ (S.ports.map (·.name)).count q.name ∧ MsgNames msg q.name) ∨
        (∃ c ∈ S.chans, 2 ≤ (S.chans.map (·.name)).count c.name ∧ MsgNames msg c.name) ∨
        ∃ b, NB S.body = .ok b ∧
          ((∃ q ∈ S.ports, q.place ∉ b.places ∧ MsgNames msg q.name) ∨
            (∃ c ∈ S.chans, c.trans ∉ b.trans.map (·.core.name) ∧ MsgNames msg c.name)))

/- The pinned readable form of MOD-006: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_006 : {N A : Type} → NetBuilder (defsTB N A) → SubnetMake N A → Prop :=
fun {N A} NB SB =>
  (∀ (S : SubnetIn N A) (b : BuiltNet N A),
      NB S.body = Except.ok b → ∀ q ∈ S.ports, q.place ∉ b.places → ∃ msg, SB S = Except.error msg) ∧
    (∀ (S : SubnetIn N A) (b : BuiltNet N A),
        NB S.body = Except.ok b →
          ∀ c ∈ S.chans, c.trans ∉ List.map (fun x => x.core.name) b.trans → ∃ msg, SB S = Except.error msg) ∧
      (∀ (S : SubnetIn N A), ¬(List.map (fun x => x.name) S.ports).Nodup → ∃ msg, SB S = Except.error msg) ∧
        (∀ (S : SubnetIn N A), ¬(List.map (fun x => x.name) S.chans).Nodup → ∃ msg, SB S = Except.error msg) ∧
          (∀ (S : SubnetIn N A) (e : String), NB S.body = Except.error e → ∃ msg, SB S = Except.error msg) ∧
            (∀ (S : SubnetIn N A) (b : BuiltNet N A),
                NB S.body = Except.ok b →
                  (∀ q ∈ S.ports, q.place ∈ b.places) →
                    (∀ c ∈ S.chans, c.trans ∈ List.map (fun x => x.core.name) b.trans) →
                      (List.map (fun x => x.name) S.ports).Nodup →
                        (List.map (fun x => x.name) S.chans).Nodup → ∃ D, SB S = Except.ok D) ∧
              ∀ (S : SubnetIn N A) (msg : String),
                SB S = Except.error msg →
                  (∃ e, NB S.body = Except.error e ∧ MsgNames msg e) ∨
                    (∃ q ∈ S.ports, 2 ≤ List.count q.name (List.map (fun x => x.name) S.ports) ∧ MsgNames msg q.name) ∨
                      (∃ c ∈ S.chans,
                          2 ≤ List.count c.name (List.map (fun x => x.name) S.chans) ∧ MsgNames msg c.name) ∨
                        ∃ b,
                          NB S.body = Except.ok b ∧
                            ((∃ q ∈ S.ports, q.place ∉ b.places ∧ MsgNames msg q.name) ∨
                              ∃ c ∈ S.chans, c.trans ∉ List.map (fun x => x.core.name) b.trans ∧ MsgNames msg c.name)
-/
#guard_msgs in #print MOD_006

/-! ### The seven lines, named (for the mutants) -/

section Lines

/-- The names of a subnet input's ports. -/
def SubnetIn.portNames (S : SubnetIn N A) : List String := S.ports.map (·.name)

/-- The names of a subnet input's channels. -/
def SubnetIn.chanNames (S : SubnetIn N A) : List String := S.chans.map (·.name)

/-- The transition names of a built net. -/
def transNames (b : BuiltNet N A) : List String := b.trans.map (·.core.name)

/-- A port offends against the built body `b`: its place is not a place of `b`, or two ports carry
its name. -/
def PortOffends (S : SubnetIn N A) (b : BuiltNet N A) (q : Port N) : Prop :=
  q.place ∉ b.places ∨ 2 ≤ S.portNames.count q.name

/-- A channel offends against the built body `b`: no transition of `b` has its transition's name,
or two channels carry its name. -/
def ChanOffends (S : SubnetIn N A) (b : BuiltNet N A) (c : Chan) : Prop :=
  c.trans ∉ transNames b ∨ 2 ≤ S.chanNames.count c.name

/-- Line 1 of MOD-006: a port on a place the built body does not hold fails. -/
def mod006_line1 (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) b, NB S.body = .ok b →
    ∀ q ∈ S.ports, q.place ∉ b.places → ∃ msg, SB S = .error msg

/-- Line 2 of MOD-006: a channel on a transition name the built body does not hold fails. -/
def mod006_line2 (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) b, NB S.body = .ok b →
    ∀ c ∈ S.chans, c.trans ∉ b.trans.map (·.core.name) → ∃ msg, SB S = .error msg

/-- Line 3 of MOD-006: two ports of one name fail. -/
def mod006_line3 (SB : SubnetMake N A) : Prop :=
  ∀ S : SubnetIn N A, ¬ (S.ports.map (·.name)).Nodup → ∃ msg, SB S = .error msg

/-- Line 4 of MOD-006: two channels of one name fail. -/
def mod006_line4 (SB : SubnetMake N A) : Prop :=
  ∀ S : SubnetIn N A, ¬ (S.chans.map (·.name)).Nodup → ∃ msg, SB S = .error msg

/-- Line 5 of MOD-006: a body the net builder rejects fails. -/
def mod006_line5 (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) e, NB S.body = .error e → ∃ msg, SB S = .error msg

/-- Line 6 of MOD-006: otherwise building succeeds. -/
def mod006_line6 (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) b, NB S.body = .ok b →
    (∀ q ∈ S.ports, q.place ∈ b.places) →
    (∀ c ∈ S.chans, c.trans ∈ b.trans.map (·.core.name)) →
    (S.ports.map (·.name)).Nodup → (S.chans.map (·.name)).Nodup → ∃ D, SB S = .ok D

/-- What line 7 asks of the message `msg` of a failure on `S`: it contains the body's rejection
message, or the name of a port or channel whose name another one carries, or (when the body
builds as `b`) the name of a port whose place `b` does not hold or of a channel whose transition
name `b` does not hold. -/
def Mod006Named (NB : NetBuilder (defsTB N A)) (S : SubnetIn N A) (msg : String) : Prop :=
  (∃ e, NB S.body = .error e ∧ MsgNames msg e) ∨
  (∃ q ∈ S.ports, 2 ≤ S.portNames.count q.name ∧ MsgNames msg q.name) ∨
  (∃ c ∈ S.chans, 2 ≤ S.chanNames.count c.name ∧ MsgNames msg c.name) ∨
  ∃ b, NB S.body = .ok b ∧
    ((∃ q ∈ S.ports, q.place ∉ b.places ∧ MsgNames msg q.name) ∨
      (∃ c ∈ S.chans, c.trans ∉ transNames b ∧ MsgNames msg c.name))

/-- Line 7 of MOD-006: a failure's message contains the body's rejection message or the name of
an offending port or channel. -/
def mod006_line7 (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) msg, SB S = .error msg → Mod006Named NB S msg

/-- A message that names a port offending against the built body meets line 7. -/
theorem mod006Named_of_port {NB : NetBuilder (defsTB N A)} {S : SubnetIn N A} {b : BuiltNet N A}
    {msg : String} (hb : NB S.body = .ok b)
    (h : ∃ q ∈ S.ports, PortOffends S b q ∧ MsgNames msg q.name) : Mod006Named NB S msg := by
  obtain ⟨q, hq, hoff | hoff, hn⟩ := h
  · exact Or.inr (Or.inr (Or.inr ⟨b, hb, Or.inl ⟨q, hq, hoff, hn⟩⟩))
  · exact Or.inr (Or.inl ⟨q, hq, hoff, hn⟩)

/-- A message that names a channel offending against the built body meets line 7. -/
theorem mod006Named_of_chan {NB : NetBuilder (defsTB N A)} {S : SubnetIn N A} {b : BuiltNet N A}
    {msg : String} (hb : NB S.body = .ok b)
    (h : ∃ c ∈ S.chans, ChanOffends S b c ∧ MsgNames msg c.name) : Mod006Named NB S msg := by
  obtain ⟨c, hc, hoff | hoff, hn⟩ := h
  · exact Or.inr (Or.inr (Or.inr ⟨b, hb, Or.inr ⟨c, hc, hoff, hn⟩⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hoff, hn⟩))

/-- MOD-006 is its seven lines. -/
theorem mod006_iff (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) :
    MOD_006 NB SB ↔ mod006_line1 NB SB ∧ mod006_line2 NB SB ∧ mod006_line3 SB ∧
      mod006_line4 SB ∧ mod006_line5 NB SB ∧ mod006_line6 NB SB ∧ mod006_line7 NB SB :=
  Iff.rfl

/-- **Line 6 follows from line 7.** When the body builds and no port or channel offends, a
failure would need a message naming an offender, and there is none; so the build succeeds. -/
theorem mod006_line6_of_line7 {NB : NetBuilder (defsTB N A)} {SB : SubnetMake N A}
    (h7 : mod006_line7 NB SB) : mod006_line6 NB SB := by
  intro S b hb hp hc hpn hcn
  cases hS : SB S with
  | ok D => exact ⟨D, rfl⟩
  | error msg =>
    exfalso
    rcases h7 S msg hS with ⟨e, he, -⟩ | ⟨q, -, hq, -⟩ | ⟨c, -, hq, -⟩ | ⟨b', hb', hq | hq⟩
    · rw [hb] at he; cases he
    · have := List.nodup_iff_count_le_one.1 hpn q.name
      unfold SubnetIn.portNames at hq; omega
    · have := List.nodup_iff_count_le_one.1 hcn c.name
      unfold SubnetIn.chanNames at hq; omega
    · rw [hb] at hb'; cases hb'
      obtain ⟨q, hqm, hoff, -⟩ := hq
      exact hoff (hp q hqm)
    · rw [hb] at hb'; cases hb'
      obtain ⟨c, hcm, hoff, -⟩ := hq
      exact hoff (hc c hcm)

end Lines

/-! ### The reference subnet builder -/

section Check

variable {α : Type}

/-- Walk a list of interface entries in declaration order with the names seen so far: an entry
whose name was seen fails with `dup`, an entry that is not `ok` fails with `bad`, otherwise its name
is recorded and the walk goes on. This is the loop of all three runtimes, for ports and for
channels. -/
def checkList (key : α → String) (ok : α → Prop) [DecidablePred ok] (dup bad : α → String) :
    List String → List α → Option String
  | _, [] => none
  | seen, x :: xs =>
    if key x ∈ seen then some (dup x)
    else if ok x then checkList key ok dup bad (key x :: seen) xs
    else some (bad x)

/-- The walk passes exactly when every entry is `ok`, no entry's name was seen before, and the
names are pairwise distinct. -/
theorem checkList_none_iff {key : α → String} {ok : α → Prop} [DecidablePred ok]
    {dup bad : α → String} :
    ∀ {seen : List String} {xs : List α}, checkList key ok dup bad seen xs = none ↔
      (∀ x ∈ xs, ok x) ∧ (∀ x ∈ xs, key x ∉ seen) ∧ (xs.map key).Nodup
  | seen, [] => by simp [checkList]
  | seen, x :: xs => by
    unfold checkList
    by_cases hs : key x ∈ seen
    · simp [hs]
    · by_cases ho : ok x
      · rw [if_neg hs, if_pos ho, checkList_none_iff]
        simp only [List.forall_mem_cons, List.map_cons, List.nodup_cons, List.mem_map,
          not_exists, not_and]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨ho, h1⟩, ⟨hs, fun y hy hm => h2 y hy (List.mem_cons_of_mem _ hm)⟩,
            fun y hy he => h2 y hy (by rw [he]; exact List.mem_cons_self), h3⟩
        · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩, h3, h4⟩
          refine ⟨h1, fun y hy hm => ?_, h4⟩
          rcases List.mem_cons.1 hm with he | he
          · exact h3 y hy he
          · exact h2 y hy he
      · simp [hs, ho]

/-- A failed walk names an entry that is not `ok`, or whose name was seen before, or whose name two
entries carry. -/
theorem checkList_some {key : α → String} {ok : α → Prop} [DecidablePred ok]
    {dup bad : α → String} :
    ∀ {seen : List String} {xs : List α} {m : String}, checkList key ok dup bad seen xs = some m →
      ∃ x ∈ xs, (¬ ok x ∨ key x ∈ seen ∨ 2 ≤ (xs.map key).count (key x)) ∧
        (m = dup x ∨ m = bad x)
  | seen, [], m, h => by simp [checkList] at h
  | seen, x :: xs, m, h => by
    unfold checkList at h
    by_cases hs : key x ∈ seen
    · rw [if_pos hs] at h; cases h
      exact ⟨x, List.mem_cons_self, Or.inr (Or.inl hs), Or.inl rfl⟩
    · rw [if_neg hs] at h
      by_cases ho : ok x
      · rw [if_pos ho] at h
        obtain ⟨y, hy, hoff, hm⟩ := checkList_some h
        refine ⟨y, List.mem_cons_of_mem _ hy, ?_, hm⟩
        rcases hoff with h1 | h2 | h3
        · exact Or.inl h1
        · rcases List.mem_cons.1 h2 with he | he
          · refine Or.inr (Or.inr ?_)
            have : 0 < (xs.map key).count (key y) :=
              List.count_pos_iff.2 (List.mem_map_of_mem hy)
            simp only [List.map_cons, List.count_cons, he, beq_self_eq_true, if_true]
            rw [← he]; omega
          · exact Or.inr (Or.inl he)
        · refine Or.inr (Or.inr ?_)
          simp only [List.map_cons, List.count_cons]
          split <;> omega
      · rw [if_neg ho] at h; cases h
        exact ⟨x, List.mem_cons_self, Or.inl ho, Or.inr rfl⟩

/-- Walk the entries in order and fail at the first that is not `ok`: `checkList` without the
duplicate-name check (for the wrong builders). -/
def checkOnly (ok : α → Prop) [DecidablePred ok] (bad : α → String) : List α → Option String
  | [] => none
  | x :: xs => if ok x then checkOnly ok bad xs else some (bad x)

/-- `checkOnly` passes exactly when every entry is `ok`. -/
theorem checkOnly_none_iff {ok : α → Prop} [DecidablePred ok] {bad : α → String} :
    ∀ {xs : List α}, checkOnly ok bad xs = none ↔ ∀ x ∈ xs, ok x
  | [] => by simp [checkOnly]
  | x :: xs => by
    unfold checkOnly
    by_cases ho : ok x
    · rw [if_pos ho, checkOnly_none_iff]; simp [ho]
    · simp [ho]

/-- A failed `checkOnly` names an entry that is not `ok`. -/
theorem checkOnly_some {ok : α → Prop} [DecidablePred ok] {bad : α → String} :
    ∀ {xs : List α} {m : String}, checkOnly ok bad xs = some m → ∃ x ∈ xs, ¬ ok x ∧ m = bad x
  | [], m, h => by simp [checkOnly] at h
  | x :: xs, m, h => by
    unfold checkOnly at h
    by_cases ho : ok x
    · rw [if_pos ho] at h
      obtain ⟨y, hy, h1, h2⟩ := checkOnly_some h
      exact ⟨y, List.mem_cons_of_mem _ hy, h1, h2⟩
    · rw [if_neg ho] at h; cases h
      exact ⟨x, List.mem_cons_self, ho, rfl⟩

end Check

section Ref

variable [ToString N]

/-- The duplicate-port message of the runtimes. -/
def dupPortMsg (sn : String) (q : Port N) : String :=
  ("Subnet '" ++ sn ++ "': duplicate port name '") ++ q.name ++ "'"

/-- The missing-place message of the runtimes. -/
def portPlaceMsg (sn : String) (q : Port N) : String :=
  ("Subnet '" ++ sn ++ "': port '") ++ q.name ++
    ("' references place '" ++ toString q.place ++ "' which is not in the body")

/-- The duplicate-channel message of the runtimes. -/
def dupChanMsg (sn : String) (c : Chan) : String :=
  ("Subnet '" ++ sn ++ "': duplicate channel name '") ++ c.name ++ "'"

/-- The missing-transition message of the runtimes. -/
def chanTransMsg (sn : String) (c : Chan) : String :=
  ("Subnet '" ++ sn ++ "': channel '") ++ c.name ++
    ("' references transition '" ++ c.trans ++ "' which is not in the body")

end Ref

/-- The subnet definition a successful build returns: the input's name, the built body's places
and terminal places, the input's transition definitions, ports and channels. -/
def builtDef (S : SubnetIn N A) (b : BuiltNet N A) : SubnetDef N A :=
  { name := S.name, places := b.places, defs := S.defs, terminals := b.terminals,
    ports := S.ports, chans := S.chans }

/-- The shape of a subnet builder: build the body with `NB` (a rejection passes its message
through), then the port check `cp`, then the channel check `cc`, both against the built body;
success returns `builtDef`. -/
def subnetVia (NB : NetBuilder (defsTB N A))
    (cp cc : SubnetIn N A → BuiltNet N A → Option String) : SubnetMake N A := fun S =>
  match NB S.body with
  | .error e => .error e
  | .ok b =>
    match cp S b with
    | some m => .error m
    | none =>
      match cc S b with
      | some m => .error m
      | none => .ok (builtDef S b)

section Ref

variable [DecidableEq N] [ToString N]

/-- The reference port check: ports in declaration order, a duplicate name first, then the place
against the built body's places (`SubnetDefBuilder::build` in `rust/libpetri-core/src/subnet_def.rs`). -/
def refPortCheck (S : SubnetIn N A) (b : BuiltNet N A) : Option String :=
  checkList (·.name) (fun q : Port N => q.place ∈ b.places) (dupPortMsg S.name)
    (portPlaceMsg S.name) [] S.ports

/-- The reference channel check: channels in declaration order, a duplicate name first, then the
transition's name against the built body's transition names (`SubnetDefBuilder::build` in `subnet_def.rs`). -/
def refChanCheck (S : SubnetIn N A) (b : BuiltNet N A) : Option String :=
  checkList (·.name) (fun c : Chan => c.trans ∈ transNames b) (dupChanMsg S.name)
    (chanTransMsg S.name) [] S.chans

/-- **The reference subnet builder.** Build the body with the net builder `NB`, then check the
ports, then the channels, as Rust, Java and TypeScript do (`SubnetDefBuilder::build` in `subnet_def.rs`,
`SubnetDef.Builder.build` in `SubnetDef.java`, `SubnetDefBuilder.build` in `subnet-def.ts`). -/
def refSubnetBuild (NB : NetBuilder (defsTB N A)) : SubnetMake N A :=
  subnetVia NB refPortCheck refChanCheck

end Ref

/- The reference subnet builder is the witness model of the subnet-definition blocks. -/
#spec_witness refSubnetBuild

/-! ### Line lemmas for every builder of the `subnetVia` shape -/

section Via

variable {NB : NetBuilder (defsTB N A)} {cp cc : SubnetIn N A → BuiltNet N A → Option String}

/-- A `subnetVia` builder fails exactly when the body fails, or the port check fails, or the
port check passes and the channel check fails. -/
theorem subnetVia_error {S : SubnetIn N A} {m : String} :
    subnetVia NB cp cc S = .error m ↔
      NB S.body = .error m ∨ ∃ b, NB S.body = .ok b ∧
        (cp S b = some m ∨ (cp S b = none ∧ cc S b = some m)) := by
  cases hb : NB S.body with
  | error e => simp [subnetVia, hb]
  | ok b =>
    cases hp : cp S b with
    | some m' => simp [subnetVia, hb, hp]
    | none => cases hc : cc S b <;> simp [subnetVia, hb, hp, hc]

/-- When the body builds as `b` and both checks pass, a `subnetVia` builder returns
`builtDef S b`. -/
theorem subnetVia_ok {S : SubnetIn N A} {b : BuiltNet N A} (hb : NB S.body = .ok b)
    (hp : cp S b = none) (hc : cc S b = none) : subnetVia NB cp cc S = .ok (builtDef S b) := by
  simp [subnetVia, hb, hp, hc]

/-- A `subnetVia` builder fails unless the body builds and both checks pass. -/
theorem subnetVia_fails {S : SubnetIn N A}
    (h : ∀ b, NB S.body = .ok b → cp S b = none → cc S b = none → False) :
    ∃ m, subnetVia NB cp cc S = .error m := by
  cases hb : NB S.body with
  | error e => exact ⟨e, by simp [subnetVia, hb]⟩
  | ok b =>
    cases hp : cp S b with
    | some m => exact ⟨m, by simp [subnetVia, hb, hp]⟩
    | none =>
      cases hc : cc S b with
      | some m => exact ⟨m, by simp [subnetVia, hb, hp, hc]⟩
      | none => exact (h b hb hp hc).elim

/-- Line 1 for a `subnetVia` builder whose passing port check means every port place is in the
body. -/
theorem via_line1 (hP : ∀ S b, cp S b = none → ∀ q ∈ S.ports, q.place ∈ b.places) :
    mod006_line1 NB (subnetVia NB cp cc) := fun S b hb q hq hn =>
  subnetVia_fails fun b' hb' hp _ => by
    rw [hb] at hb'; cases hb'; exact hn (hP S b hp q hq)

/-- Line 2 for a `subnetVia` builder whose passing channel check means every channel's
transition is in the body. -/
theorem via_line2 (hC : ∀ S b, cc S b = none → ∀ c ∈ S.chans, c.trans ∈ transNames b) :
    mod006_line2 NB (subnetVia NB cp cc) := fun S b hb c hc hn =>
  subnetVia_fails fun b' hb' _ hcc => by
    rw [hb] at hb'; cases hb'; exact hn (hC S b hcc c hc)

/-- Line 3 for a `subnetVia` builder whose passing port check means distinct port names. -/
theorem via_line3 (hP : ∀ S b, cp S b = none → (S.ports.map (·.name)).Nodup) :
    mod006_line3 (subnetVia NB cp cc) := fun S hn =>
  subnetVia_fails fun b _ hp _ => hn (hP S b hp)

/-- Line 4 for a `subnetVia` builder whose passing channel check means distinct channel names. -/
theorem via_line4 (hC : ∀ S b, cc S b = none → (S.chans.map (·.name)).Nodup) :
    mod006_line4 (subnetVia NB cp cc) := fun S hn =>
  subnetVia_fails fun b _ _ hc => hn (hC S b hc)

/-- Line 5 holds for every `subnetVia` builder. -/
theorem via_line5 : mod006_line5 NB (subnetVia NB cp cc) := fun S e he =>
  subnetVia_fails fun b hb _ _ => by rw [he] at hb; cases hb

/-- Line 7 for a `subnetVia` builder whose failing checks name an offender. -/
theorem via_line7
    (hP : ∀ S b m, cp S b = some m → ∃ q ∈ S.ports, PortOffends S b q ∧ MsgNames m q.name)
    (hC : ∀ S b m, cc S b = some m → ∃ c ∈ S.chans, ChanOffends S b c ∧ MsgNames m c.name) :
    mod006_line7 NB (subnetVia NB cp cc) := by
  intro S m h
  rcases subnetVia_error.1 h with he | ⟨b, hb, hp | ⟨-, hc⟩⟩
  · exact Or.inl ⟨m, he, msgNames_self m⟩
  · exact mod006Named_of_port hb (hP S b m hp)
  · exact mod006Named_of_chan hb (hC S b m hc)

end Via

/-! ### The reference checks -/

section RefChecks

variable [DecidableEq N] [ToString N]

/-- The reference port check passes exactly when every port's place is in the body and the port
names are distinct. -/
theorem refPortCheck_none (S : SubnetIn N A) (b : BuiltNet N A) :
    refPortCheck S b = none ↔ (∀ q ∈ S.ports, q.place ∈ b.places) ∧ (S.ports.map (·.name)).Nodup := by
  unfold refPortCheck
  rw [checkList_none_iff]
  simp

omit [DecidableEq N] [ToString N] in
/-- The reference channel check passes exactly when every channel's transition is in the body
and the channel names are distinct. -/
theorem refChanCheck_none (S : SubnetIn N A) (b : BuiltNet N A) :
    refChanCheck S b = none ↔
      (∀ c ∈ S.chans, c.trans ∈ transNames b) ∧ (S.chans.map (·.name)).Nodup := by
  unfold refChanCheck
  rw [checkList_none_iff]
  simp

/-- A failed reference port check names an offending port. -/
theorem refPortCheck_some (S : SubnetIn N A) (b : BuiltNet N A) (m : String)
    (h : refPortCheck S b = some m) : ∃ q ∈ S.ports, PortOffends S b q ∧ MsgNames m q.name := by
  obtain ⟨q, hq, hoff, hm⟩ := checkList_some h
  refine ⟨q, hq, ?_, ?_⟩
  · rcases hoff with h1 | h2 | h3
    · exact Or.inl h1
    · cases h2
    · exact Or.inr h3
  · rcases hm with rfl | rfl
    · exact msgNames_mid _ _ _
    · exact msgNames_mid _ _ _

omit [DecidableEq N] [ToString N] in
/-- A failed reference channel check names an offending channel. -/
theorem refChanCheck_some (S : SubnetIn N A) (b : BuiltNet N A) (m : String)
    (h : refChanCheck S b = some m) : ∃ c ∈ S.chans, ChanOffends S b c ∧ MsgNames m c.name := by
  obtain ⟨c, hc, hoff, hm⟩ := checkList_some h
  refine ⟨c, hc, ?_, ?_⟩
  · rcases hoff with h1 | h2 | h3
    · exact Or.inl h1
    · cases h2
    · exact Or.inr h3
  · rcases hm with rfl | rfl
    · exact msgNames_mid _ _ _
    · exact msgNames_mid _ _ _

end RefChecks

/-! ### The reference -/

/-- ✓ The reference subnet builder satisfies MOD-006 for every net builder: it builds the body
first, rejects a port on a place the built body does not hold, a channel on a transition name it
does not hold, two ports or two channels of one name and a body the net builder rejects, builds
everything else, and every message it fails with is the body's own or names the port or channel
it stopped at. -/
@[evidence holds MOD_006]
theorem MOD_006_reference {N A : Type} [DecidableEq N] [ToString N]
    (NB : NetBuilder (defsTB N A)) : MOD_006 NB (refSubnetBuild NB) := by
  refine ⟨via_line1 fun S b h => ((refPortCheck_none S b).1 h).1,
    via_line2 fun S b h => ((refChanCheck_none S b).1 h).1,
    via_line3 fun S b h => ((refPortCheck_none S b).1 h).2,
    via_line4 fun S b h => ((refChanCheck_none S b).1 h).2,
    via_line5, ?_, via_line7 refPortCheck_some refChanCheck_some⟩
  intro S b hb hp hc hpn hcn
  exact ⟨_, subnetVia_ok hb ((refPortCheck_none S b).2 ⟨hp, hpn⟩)
    ((refChanCheck_none S b).2 ⟨hc, hcn⟩)⟩

/-! ### Joint with CORE-040: the body is the collected net -/

/-- **The body of lines 1 and 6 is CORE-040's net.** For every net builder that meets CORE-040
and every subnet builder that meets MOD-006 over it: a port on a place that the body neither
declares nor names by an arc fails; and a body without terminal places, with distinct transition
names, whose ports sit on declared or arc-named places, whose channels name body transitions and
whose port and channel names are distinct, builds. So a port on the place `done` that only an
output arc names is accepted, and a port on a place `nowhere` that nothing names fails. -/
theorem mod006_core040 [DecidableEq N] {NB : NetBuilder (defsTB N A)} {SB : SubnetMake N A}
    (hc : CORE_040 (defsTB N A) NB) (hm : MOD_006 NB SB) (S : SubnetIn N A) :
    (∀ q ∈ S.ports, ¬ core040Coll (defsTB N A) S.body q.place → ∃ msg, SB S = .error msg) ∧
    (S.terminals = [] → (S.defs.map (·.core.name)).Nodup →
      (∀ q ∈ S.ports, core040Coll (defsTB N A) S.body q.place) →
      (∀ c ∈ S.chans, c.trans ∈ S.defs.map (·.core.name)) →
      (S.ports.map (·.name)).Nodup → (S.chans.map (·.name)).Nodup → ∃ D, SB S = .ok D) := by
  refine ⟨fun q hq hn => ?_, fun ht hdn hp hch hpn hcn => ?_⟩
  · cases hb : NB S.body with
    | error e => exact hm.2.2.2.2.1 S e hb
    | ok b => exact hm.1 S b hb q hq fun hin => hn ((hc.2.2.1 S.body b hb).1 _ hin)
  · obtain ⟨b, hb⟩ := hc.2.2.2 S.body ht
    have htr : b.trans = S.defs.map (·.toTransDef) := hc.1 S.body b hb hdn
    refine hm.2.2.2.2.2.1 S b hb (fun q hq => hc.2.1 S.body b hb _ (hp q hq)) (fun c hcm => ?_)
      hpn hcn
    rw [htr, List.map_map]
    exact hch c hcm

/-! ### Joint with EXEC-042: a terminal place is no reason to reject -/

/-- **A declared terminal place is not by itself a reason to reject the subnet.** For every net
builder that meets EXEC-042's build block and every subnet builder that meets MOD-006 over it: when
no body transition consumes from or reads a declared terminal place, the body builds, it keeps the
declared terminal places, and a subnet over it whose ports and channels are fine builds. So `buf`
with `done` declared terminal, a place `take` only produces into, builds; `instantiate` and
composition are the ones that refuse it ([EXEC-042] AC6, [MOD-010]). -/
theorem mod006_exec042 [DecidableEq N] {NB : NetBuilder (defsTB N A)} {SB : SubnetMake N A}
    (he : EXEC_042_build (defsTB N A) NB) (hm : MOD_006 NB SB) (S : SubnetIn N A)
    (hc : ¬ S.body.TerminalClash) :
    ∃ b, NB S.body = .ok b ∧ (∀ p, p ∈ b.terminals ↔ p ∈ S.terminals) ∧
      ((∀ q ∈ S.ports, q.place ∈ b.places) → (∀ c ∈ S.chans, c.trans ∈ transNames b) →
        (S.ports.map (·.name)).Nodup → (S.chans.map (·.name)).Nodup → ∃ D, SB S = .ok D) := by
  obtain ⟨b, hb⟩ := (he S.body).2.1 hc
  exact ⟨b, hb, (he S.body).2.2 b hb, fun hp hcc hpn hcn => hm.2.2.2.2.2.1 S b hb hp hcc hpn hcn⟩

/-! ### Example -/

/-- The example body transition `take`: an input arc on `slots` and the output place `done`. -/
def mod006_take : CDef String Unit :=
  { core := ⟨"take", [⟨"slots", .one⟩], [], [], []⟩, out := some (.place "done"),
    timing := .immediate, priority := 0, action := .passthrough }

/-- The example subnet `buf`: the declared place `slots`, the transition `take`, the port `in` on
`slots`, the port `out` on `done` (a place only an arc names) and the channel `go` on `take`. -/
def mod006_exS : SubnetIn String Unit :=
  { name := "buf", places := ["slots"], defs := [mod006_take],
    ports := [⟨"in", .input, "slots"⟩, ⟨"out", .output, "done"⟩], chans := [⟨"go", "take"⟩] }

/-- `buf` with its port `in` on the place `nowhere`, which the body does not hold. -/
def mod006_exBadPort : SubnetIn String Unit :=
  { mod006_exS with ports := [⟨"in", .input, "nowhere"⟩] }

/-- `buf` with two ports named `in`. -/
def mod006_exDupPort : SubnetIn String Unit :=
  { mod006_exS with ports := [⟨"in", .input, "slots"⟩, ⟨"in", .output, "done"⟩] }

/-- `buf` with its channel `go` on the transition name `missing`. -/
def mod006_exBadChan : SubnetIn String Unit :=
  { mod006_exS with chans := [⟨"go", "missing"⟩] }

/-- `buf` with two channels named `go`. -/
def mod006_exDupChan : SubnetIn String Unit :=
  { mod006_exS with chans := [⟨"go", "take"⟩, ⟨"go", "take"⟩] }

/-- `buf` declaring `slots` a terminal place, which `take` consumes from: the net builder rejects
the body ([EXEC-042] AC5). -/
def mod006_exClash : SubnetIn String Unit :=
  { mod006_exS with terminals := ["slots"] }

/-- `buf` declaring `done` a terminal place, which `take` only produces into: no clash. -/
def mod006_exTerm : SubnetIn String Unit :=
  { mod006_exS with terminals := ["done"] }

/-- ✓ Every line of MOD-006 is exercised by the reference over the reference net builder. The
subnet `buf` builds, and its built body holds `done`, the place only an output arc names (line
6); it still builds with `done` declared a terminal place. Moving the port `in` to `nowhere`
fails with "Subnet 'buf': port 'in' references place 'nowhere' which is not in the body" (lines 1
and 7). Two ports named `in` fail with "Subnet 'buf': duplicate port name 'in'" (line 3). A
channel `go` on `missing` and two channels named `go` fail naming `go` (lines 2 and 4). Declaring
`slots`, which `take` consumes from, a terminal place makes the net builder reject the body, and
building the subnet fails with the net builder's message (line 5). -/
@[evidence nonvacuous MOD_006]
theorem MOD_006_nonvacuous :
    (∃ D, refSubnetBuild refNetBuild mod006_exS = .ok D ∧ "done" ∈ D.places) ∧
    (∃ D, refSubnetBuild refNetBuild mod006_exTerm = .ok D ∧ D.terminals = ["done"]) ∧
    refSubnetBuild refNetBuild mod006_exBadPort =
      .error (portPlaceMsg "buf" (⟨"in", .input, "nowhere"⟩ : Port String)) ∧
    refSubnetBuild refNetBuild mod006_exDupPort =
      .error (dupPortMsg "buf" (⟨"in", .output, "done"⟩ : Port String)) ∧
    refSubnetBuild refNetBuild mod006_exBadChan = .error (chanTransMsg "buf" ⟨"go", "missing"⟩) ∧
    refSubnetBuild refNetBuild mod006_exDupChan = .error (dupChanMsg "buf" ⟨"go", "take"⟩) ∧
    refSubnetBuild refNetBuild mod006_exClash = .error "EXEC-042" := by
  refine ⟨⟨_, rfl, by decide⟩, ⟨_, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Wrong subnet builders -/

/-- A subnet builder that accepts everything and leaves every check to instantiation. -/
def lazySB : SubnetMake N A := fun S =>
  .ok { name := S.name, places := S.places, defs := S.defs, terminals := S.terminals,
        ports := S.ports, chans := S.chans }

/-- A subnet builder that rejects everything. -/
def rejectAllSB : SubnetMake N A := fun _ => .error "rejected"

/-- Keep the first port of each name and drop the later ones silently. -/
def firstPortPerName (ps : List (Port N)) : List (Port N) :=
  ps.foldl (fun acc q => if acc.any (·.name == q.name) then acc else acc ++ [q]) []

/-- A subnet builder that drops the second of two same-named ports and builds the rest with the
reference. -/
def dropSecondPortSB [DecidableEq N] [ToString N] (NB : NetBuilder (defsTB N A)) :
    SubnetMake N A := fun S =>
  refSubnetBuild NB { S with ports := firstPortPerName S.ports }

/-- ✗ A builder that defers every check to instantiation violates MOD-006 (line 1, AC1): it
builds `buf` with its port `in` on the place `nowhere`, which the body does not hold. -/
@[evidence forbids MOD_006]
theorem MOD_006_forbids_lazy : ¬ MOD_006 refNetBuild (lazySB (N := String) (A := Unit)) := by
  intro h
  obtain ⟨msg, hm⟩ := h.1 mod006_exBadPort _ (refNetBuild_of_terminals_nil rfl)
    ⟨"in", .input, "nowhere"⟩ (by simp [mod006_exBadPort]) (by decide)
  cases hm

/-- ✗ A builder that rejects everything violates MOD-006 (line 6): it rejects `buf`, whose body
builds and whose ports and channel are all fine. -/
@[evidence forbids MOD_006]
theorem MOD_006_forbids_rejectAll :
    ¬ MOD_006 refNetBuild (rejectAllSB (N := String) (A := Unit)) := by
  intro h
  obtain ⟨D, hD⟩ := h.2.2.2.2.2.1 mod006_exS _ (refNetBuild_of_terminals_nil rfl)
    (by decide) (by decide) (by decide) (by decide)
  cases hD

/-- ✗ A builder that silently drops the second of two same-named ports violates MOD-006 (line 3):
it builds `buf` with two ports named `in`, keeping the first. -/
@[evidence forbids MOD_006]
theorem MOD_006_forbids_dropSecondPort :
    ¬ MOD_006 refNetBuild (dropSecondPortSB (N := String) (A := Unit) refNetBuild) := by
  intro h
  obtain ⟨msg, hm⟩ := h.2.2.1 mod006_exDupPort (by decide)
  have : dropSecondPortSB refNetBuild mod006_exDupPort = .ok _ := rfl
  rw [this] at hm; cases hm

/-! ### A builder that checks the names first -/

section NamesFirst

variable [DecidableEq N] [ToString N]

/-- A subnet builder that checks duplicate port names and duplicate channel names before it builds
the body ("cheap checks first"), then runs the reference. -/
def namesFirstSB (NB : NetBuilder (defsTB N A)) : SubnetMake N A := fun S =>
  match checkList (·.name) (fun _ : Port N => True) (dupPortMsg S.name) (portPlaceMsg S.name)
      [] S.ports with
  | some m => .error m
  | none =>
    match checkList (·.name) (fun _ : Chan => True) (dupChanMsg S.name) (chanTransMsg S.name)
        [] S.chans with
    | some m => .error m
    | none => refSubnetBuild NB S

/-- Where the reference fails, the names-first builder fails too. -/
theorem namesFirstSB_fails {NB : NetBuilder (defsTB N A)} {S : SubnetIn N A}
    (h : ∃ m, refSubnetBuild NB S = .error m) : ∃ m, namesFirstSB NB S = .error m := by
  unfold namesFirstSB
  cases checkList (·.name) (fun _ : Port N => True) (dupPortMsg S.name) (portPlaceMsg S.name)
      [] S.ports with
  | some m => exact ⟨m, rfl⟩
  | none =>
    cases checkList (·.name) (fun _ : Chan => True) (dupChanMsg S.name) (chanTransMsg S.name)
        [] S.chans with
    | some m => exact ⟨m, rfl⟩
    | none => exact h

/-- With distinct port names and distinct channel names, the names-first builder is the
reference. -/
theorem namesFirstSB_eq {NB : NetBuilder (defsTB N A)} {S : SubnetIn N A}
    (hp : (S.ports.map (·.name)).Nodup) (hc : (S.chans.map (·.name)).Nodup) :
    namesFirstSB NB S = refSubnetBuild NB S := by
  have hp' : checkList (·.name) (fun _ : Port N => True) (dupPortMsg S.name)
      (portPlaceMsg S.name) [] S.ports = none := checkList_none_iff.2 ⟨by simp, by simp, hp⟩
  have hc' : checkList (·.name) (fun _ : Chan => True) (dupChanMsg S.name)
      (chanTransMsg S.name) [] S.chans = none := checkList_none_iff.2 ⟨by simp, by simp, hc⟩
  simp only [namesFirstSB, hp', hc']

/-- The names-first builder meets MOD-006 for every net builder. -/
theorem namesFirstSB_meets (NB : NetBuilder (defsTB N A)) : MOD_006 NB (namesFirstSB NB) := by
  have R := MOD_006_reference (N := N) (A := A) NB
  refine ⟨fun S b hb q hq hn => namesFirstSB_fails (R.1 S b hb q hq hn),
    fun S b hb c hc hn => namesFirstSB_fails (R.2.1 S b hb c hc hn),
    fun S hn => namesFirstSB_fails (R.2.2.1 S hn),
    fun S hn => namesFirstSB_fails (R.2.2.2.1 S hn),
    fun S e he => namesFirstSB_fails (R.2.2.2.2.1 S e he),
    fun S b hb hp hc hpn hcn => by
      rw [namesFirstSB_eq hpn hcn]; exact R.2.2.2.2.2.1 S b hb hp hc hpn hcn, ?_⟩
  intro S msg h
  unfold namesFirstSB at h
  cases hp : checkList (·.name) (fun _ : Port N => True) (dupPortMsg S.name)
      (portPlaceMsg S.name) [] S.ports with
  | some m =>
    rw [hp] at h; cases h
    obtain ⟨q, hq, hoff, hm⟩ := checkList_some hp
    refine Or.inr (Or.inl ⟨q, hq, ?_, ?_⟩)
    · rcases hoff with h1 | h2 | h3
      · exact absurd trivial h1
      · cases h2
      · exact h3
    · rcases hm with rfl | rfl <;> exact msgNames_mid _ _ _
  | none =>
    rw [hp] at h
    cases hc : checkList (·.name) (fun _ : Chan => True) (dupChanMsg S.name)
        (chanTransMsg S.name) [] S.chans with
    | some m =>
      rw [hc] at h; cases h
      obtain ⟨c, hcm, hoff, hm⟩ := checkList_some hc
      refine Or.inr (Or.inr (Or.inl ⟨c, hcm, ?_, ?_⟩))
      · rcases hoff with h1 | h2 | h3
        · exact absurd trivial h1
        · cases h2
        · exact h3
      · rcases hm with rfl | rfl <;> exact msgNames_mid _ _ _
    | none =>
      rw [hc] at h
      exact R.2.2.2.2.2.2 S msg h

end NamesFirst

/-- `buf` with `slots` declared terminal, which the net builder rejects, and two ports named
`in`. -/
def mod006_exClashDup : SubnetIn String Unit :=
  { mod006_exClash with ports := [⟨"in", .input, "slots"⟩, ⟨"in", .output, "done"⟩] }

/-- ✓ MOD-006 does not fix the order of the checks. A builder that looks for duplicate port and
channel names before it builds the body meets it. Given `buf` with two ports named `in` and a
body the net builder rejects (`slots` is terminal and `take` consumes from it), that builder fails
with "Subnet 'buf': duplicate port name 'in'", where the reference fails with the net builder's
message: both name an offender. -/
@[evidence allows MOD_006]
theorem MOD_006_allows_namesFirst :
    MOD_006 refNetBuild (namesFirstSB (N := String) (A := Unit) refNetBuild) ∧
      namesFirstSB refNetBuild mod006_exClashDup =
        .error (dupPortMsg "buf" (⟨"in", .output, "done"⟩ : Port String)) ∧
      refSubnetBuild refNetBuild mod006_exClashDup = .error "EXEC-042" :=
  ⟨namesFirstSB_meets _, rfl, rfl⟩

/-! ### Mutants, one per load-bearing line -/

/-- Mutant reading: MOD-006 without line 1 (no port-place check). -/
def MOD_006_mutant_noPortPlace (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod006_line2 NB SB ∧ mod006_line3 SB ∧ mod006_line4 SB ∧ mod006_line5 NB SB ∧
    mod006_line6 NB SB ∧ mod006_line7 NB SB

/-- Mutant reading: MOD-006 without line 2 (no channel-transition check). -/
def MOD_006_mutant_noChanTrans (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod006_line1 NB SB ∧ mod006_line3 SB ∧ mod006_line4 SB ∧ mod006_line5 NB SB ∧
    mod006_line6 NB SB ∧ mod006_line7 NB SB

/-- Mutant reading: MOD-006 without line 3 (no duplicate-port check). -/
def MOD_006_mutant_noDupPort (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod006_line1 NB SB ∧ mod006_line2 NB SB ∧ mod006_line4 SB ∧ mod006_line5 NB SB ∧
    mod006_line6 NB SB ∧ mod006_line7 NB SB

/-- Mutant reading: MOD-006 without line 4 (no duplicate-channel check). -/
def MOD_006_mutant_noDupChan (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod006_line1 NB SB ∧ mod006_line2 NB SB ∧ mod006_line3 SB ∧ mod006_line5 NB SB ∧
    mod006_line6 NB SB ∧ mod006_line7 NB SB

/-- Mutant reading: MOD-006 without line 5 (a body rejection need not reject the subnet). -/
def MOD_006_mutant_noBody (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod006_line1 NB SB ∧ mod006_line2 NB SB ∧ mod006_line3 SB ∧ mod006_line4 SB ∧
    mod006_line6 NB SB ∧ mod006_line7 NB SB

/-- Mutant reading: MOD-006 without line 7 (a failure's message need not name anything). -/
def MOD_006_mutant_anyMessage (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod006_line1 NB SB ∧ mod006_line2 NB SB ∧ mod006_line3 SB ∧ mod006_line4 SB ∧
    mod006_line5 NB SB ∧ mod006_line6 NB SB

section MutantModels

variable [DecidableEq N] [ToString N]

/-- The port check without the place test: duplicate names only. -/
def noPlacePortCheck (S : SubnetIn N A) (_ : BuiltNet N A) : Option String :=
  checkList (·.name) (fun _ : Port N => True) (dupPortMsg S.name) (portPlaceMsg S.name) [] S.ports

/-- The channel check without the transition test: duplicate names only. -/
def noTransChanCheck (S : SubnetIn N A) (_ : BuiltNet N A) : Option String :=
  checkList (·.name) (fun _ : Chan => True) (dupChanMsg S.name) (chanTransMsg S.name) [] S.chans

/-- The port check without the duplicate-name test: places only. -/
def noDupPortCheck (S : SubnetIn N A) (b : BuiltNet N A) : Option String :=
  checkOnly (fun q : Port N => q.place ∈ b.places) (portPlaceMsg S.name) S.ports

/-- The channel check without the duplicate-name test: transitions only. -/
def noDupChanCheck (S : SubnetIn N A) (b : BuiltNet N A) : Option String :=
  checkOnly (fun c : Chan => c.trans ∈ transNames b) (chanTransMsg S.name) S.chans

/-- The subnet message that names no port and no channel. -/
def subnetOnlyMsg (sn : String) : String := "Subnet '" ++ sn ++ "' is invalid"

/-- The reference port check with a message that names the subnet only. -/
def subnetMsgPortCheck (S : SubnetIn N A) (b : BuiltNet N A) : Option String :=
  checkList (·.name) (fun q : Port N => q.place ∈ b.places) (fun _ => subnetOnlyMsg S.name)
    (fun _ => subnetOnlyMsg S.name) [] S.ports

/-- The reference channel check with a message that names the subnet only. -/
def subnetMsgChanCheck (S : SubnetIn N A) (b : BuiltNet N A) : Option String :=
  checkList (·.name) (fun c : Chan => c.trans ∈ transNames b) (fun _ => subnetOnlyMsg S.name)
    (fun _ => subnetOnlyMsg S.name) [] S.chans

/-- A builder that swallows the body's rejection: when the net builder rejects the body and the
port and channel names are distinct, it builds over an empty body; otherwise it is the reference. -/
def swallowBodySB (NB : NetBuilder (defsTB N A)) : SubnetMake N A := fun S =>
  match NB S.body with
  | .error e =>
    if (S.ports.map (·.name)).Nodup ∧ (S.chans.map (·.name)).Nodup then .ok (builtDef S ⟨[], [], []⟩)
    else .error e
  | .ok _ => refSubnetBuild NB S

/-- Where the body builds, the swallowing builder is the reference. -/
theorem swallowBodySB_ok {NB : NetBuilder (defsTB N A)} {S : SubnetIn N A} {b : BuiltNet N A}
    (hb : NB S.body = .ok b) : swallowBodySB NB S = refSubnetBuild NB S := by
  simp [swallowBodySB, hb]

end MutantModels

/-- The mutant without line 1 is killed by the builder without the place test: it meets every
other line, but builds `buf` with its port `in` on `nowhere`. -/
@[evidence mutant MOD_006]
theorem MOD_006_mutant_noPortPlace_killed :
    MOD_006_mutant_noPortPlace refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild noPlacePortCheck refChanCheck) ∧
      ¬ MOD_006 refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild noPlacePortCheck refChanCheck) := by
  have hP : ∀ (S : SubnetIn String Unit) b, noPlacePortCheck S b = none ↔
      (S.ports.map (·.name)).Nodup := fun S b => by
    unfold noPlacePortCheck; rw [checkList_none_iff]; simp
  refine ⟨⟨via_line2 fun S b h => ((refChanCheck_none S b).1 h).1,
    via_line3 fun S b h => (hP S b).1 h,
    via_line4 fun S b h => ((refChanCheck_none S b).1 h).2, via_line5,
    fun S b hb _ hc hpn hcn => ⟨_, subnetVia_ok hb ((hP S b).2 hpn)
      ((refChanCheck_none S b).2 ⟨hc, hcn⟩)⟩,
    via_line7 (fun S b m h => ?_) refChanCheck_some⟩, fun h => ?_⟩
  · obtain ⟨q, hq, hoff, hm⟩ := checkList_some h
    refine ⟨q, hq, ?_, ?_⟩
    · rcases hoff with h1 | h2 | h3
      · exact absurd trivial h1
      · cases h2
      · exact Or.inr h3
    · rcases hm with rfl | rfl <;> exact msgNames_mid _ _ _
  · obtain ⟨msg, hm⟩ := h.1 mod006_exBadPort _ (refNetBuild_of_terminals_nil rfl)
      ⟨"in", .input, "nowhere"⟩ (by simp [mod006_exBadPort]) (by decide)
    have : subnetVia refNetBuild noPlacePortCheck refChanCheck mod006_exBadPort = .ok _ := rfl
    rw [this] at hm; cases hm

/-- The mutant without line 2 is killed by the builder without the transition test: it meets
every other line, but builds `buf` with its channel `go` on `missing`. -/
@[evidence mutant MOD_006]
theorem MOD_006_mutant_noChanTrans_killed :
    MOD_006_mutant_noChanTrans refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild refPortCheck noTransChanCheck) ∧
      ¬ MOD_006 refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild refPortCheck noTransChanCheck) := by
  have hC : ∀ (S : SubnetIn String Unit) b, noTransChanCheck S b = none ↔
      (S.chans.map (·.name)).Nodup := fun S b => by
    unfold noTransChanCheck; rw [checkList_none_iff]; simp
  refine ⟨⟨via_line1 fun S b h => ((refPortCheck_none S b).1 h).1,
    via_line3 fun S b h => ((refPortCheck_none S b).1 h).2,
    via_line4 fun S b h => (hC S b).1 h, via_line5,
    fun S b hb hp _ hpn hcn => ⟨_, subnetVia_ok hb ((refPortCheck_none S b).2 ⟨hp, hpn⟩)
      ((hC S b).2 hcn)⟩,
    via_line7 refPortCheck_some (fun S b m h => ?_)⟩, fun h => ?_⟩
  · obtain ⟨c, hc, hoff, hm⟩ := checkList_some h
    refine ⟨c, hc, ?_, ?_⟩
    · rcases hoff with h1 | h2 | h3
      · exact absurd trivial h1
      · cases h2
      · exact Or.inr h3
    · rcases hm with rfl | rfl <;> exact msgNames_mid _ _ _
  · obtain ⟨msg, hm⟩ := h.2.1 mod006_exBadChan _ (refNetBuild_of_terminals_nil rfl)
      ⟨"go", "missing"⟩ (by decide) (by decide)
    have : subnetVia refNetBuild refPortCheck noTransChanCheck mod006_exBadChan = .ok _ := rfl
    rw [this] at hm; cases hm

/-- The mutant without line 3 is killed by the builder without the duplicate-port test: it meets
every other line, but builds `buf` with two ports named `in`, both on body places. -/
@[evidence mutant MOD_006]
theorem MOD_006_mutant_noDupPort_killed :
    MOD_006_mutant_noDupPort refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild noDupPortCheck refChanCheck) ∧
      ¬ MOD_006 refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild noDupPortCheck refChanCheck) := by
  have hP : ∀ (S : SubnetIn String Unit) b, noDupPortCheck S b = none ↔
      ∀ q ∈ S.ports, q.place ∈ b.places := fun S b => by
    unfold noDupPortCheck; rw [checkOnly_none_iff]
  refine ⟨⟨via_line1 fun S b h => (hP S b).1 h,
    via_line2 fun S b h => ((refChanCheck_none S b).1 h).1,
    via_line4 fun S b h => ((refChanCheck_none S b).1 h).2, via_line5,
    fun S b hb hp hc _ hcn => ⟨_, subnetVia_ok hb ((hP S b).2 hp)
      ((refChanCheck_none S b).2 ⟨hc, hcn⟩)⟩,
    via_line7 (fun S b m h => ?_) refChanCheck_some⟩, fun h => ?_⟩
  · obtain ⟨q, hq, hoff, rfl⟩ := checkOnly_some h
    exact ⟨q, hq, Or.inl hoff, msgNames_mid _ _ _⟩
  · obtain ⟨msg, hm⟩ := h.2.2.1 mod006_exDupPort (by decide)
    have : subnetVia refNetBuild noDupPortCheck refChanCheck mod006_exDupPort = .ok _ := rfl
    rw [this] at hm; cases hm

/-- The mutant without line 4 is killed by the builder without the duplicate-channel test: it
meets every other line, but builds `buf` with two channels named `go`, both on `take`. -/
@[evidence mutant MOD_006]
theorem MOD_006_mutant_noDupChan_killed :
    MOD_006_mutant_noDupChan refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild refPortCheck noDupChanCheck) ∧
      ¬ MOD_006 refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild refPortCheck noDupChanCheck) := by
  have hC : ∀ (S : SubnetIn String Unit) b, noDupChanCheck S b = none ↔
      ∀ c ∈ S.chans, c.trans ∈ transNames b := fun S b => by
    unfold noDupChanCheck; rw [checkOnly_none_iff]
  refine ⟨⟨via_line1 fun S b h => ((refPortCheck_none S b).1 h).1,
    via_line2 fun S b h => (hC S b).1 h,
    via_line3 fun S b h => ((refPortCheck_none S b).1 h).2, via_line5,
    fun S b hb hp hc hpn _ => ⟨_, subnetVia_ok hb ((refPortCheck_none S b).2 ⟨hp, hpn⟩)
      ((hC S b).2 hc)⟩,
    via_line7 refPortCheck_some (fun S b m h => ?_)⟩, fun h => ?_⟩
  · obtain ⟨c, hc, hoff, rfl⟩ := checkOnly_some h
    exact ⟨c, hc, Or.inl hoff, msgNames_mid _ _ _⟩
  · obtain ⟨msg, hm⟩ := h.2.2.2.1 mod006_exDupChan (by decide)
    have : subnetVia refNetBuild refPortCheck noDupChanCheck mod006_exDupChan = .ok _ := rfl
    rw [this] at hm; cases hm

/-- The mutant without line 5 is killed by the builder that swallows the body's rejection: it
meets every other line, but builds `buf` with `slots` declared terminal, a body the net builder
rejects because `take` consumes from `slots`. -/
@[evidence mutant MOD_006]
theorem MOD_006_mutant_noBody_killed :
    MOD_006_mutant_noBody refNetBuild (swallowBodySB (N := String) (A := Unit) refNetBuild) ∧
      ¬ MOD_006 refNetBuild (swallowBodySB (N := String) (A := Unit) refNetBuild) := by
  have R := MOD_006_reference (N := String) (A := Unit) refNetBuild
  refine ⟨⟨fun S b hb q hq hn => ?_, fun S b hb c hc hn => ?_, fun S hn => ?_, fun S hn => ?_,
    fun S b hb hp hc hpn hcn => ?_, fun S m h => ?_⟩, fun h => ?_⟩
  · rw [swallowBodySB_ok hb]; exact R.1 S b hb q hq hn
  · rw [swallowBodySB_ok hb]; exact R.2.1 S b hb c hc hn
  · cases hb : refNetBuild S.body with
    | error e => exact ⟨e, by simp [swallowBodySB, hb, hn]⟩
    | ok b => rw [swallowBodySB_ok hb]; exact R.2.2.1 S hn
  · cases hb : refNetBuild S.body with
    | error e => exact ⟨e, by simp [swallowBodySB, hb, hn]⟩
    | ok b => rw [swallowBodySB_ok hb]; exact R.2.2.2.1 S hn
  · rw [swallowBodySB_ok hb]; exact R.2.2.2.2.2.1 S b hb hp hc hpn hcn
  · cases hb : refNetBuild S.body with
    | error e =>
      have h' := h
      simp only [swallowBodySB, hb] at h'
      split at h'
      · cases h'
      · cases h'; exact Or.inl ⟨_, hb, msgNames_self _⟩
    | ok b =>
      rw [swallowBodySB_ok hb] at h
      exact R.2.2.2.2.2.2 S m h
  · obtain ⟨msg, hm⟩ := h.2.2.2.2.1 mod006_exClash "EXEC-042" rfl
    have : swallowBodySB refNetBuild mod006_exClash = .ok _ := rfl
    rw [this] at hm; cases hm

/-- The example with one port `x` on `nowhere` and no channel. -/
def mod006_exBadX : SubnetIn String Unit :=
  { mod006_exS with ports := [⟨"x", .input, "nowhere"⟩], chans := [] }

/-- The mutant without line 7 is killed by the builder whose messages name the subnet only: it
meets every other line, but rejects `buf` with its port `x` on `nowhere` with "Subnet 'buf' is
invalid", which names neither the port `x` nor the body's message. -/
@[evidence mutant MOD_006]
theorem MOD_006_mutant_anyMessage_killed :
    MOD_006_mutant_anyMessage refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild subnetMsgPortCheck subnetMsgChanCheck) ∧
      ¬ MOD_006 refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild subnetMsgPortCheck subnetMsgChanCheck) := by
  have hP : ∀ (S : SubnetIn String Unit) b, subnetMsgPortCheck S b = none ↔
      (∀ q ∈ S.ports, q.place ∈ b.places) ∧ (S.ports.map (·.name)).Nodup := fun S b => by
    unfold subnetMsgPortCheck; rw [checkList_none_iff]; simp
  have hC : ∀ (S : SubnetIn String Unit) b, subnetMsgChanCheck S b = none ↔
      (∀ c ∈ S.chans, c.trans ∈ transNames b) ∧ (S.chans.map (·.name)).Nodup := fun S b => by
    unfold subnetMsgChanCheck; rw [checkList_none_iff]; simp
  refine ⟨⟨via_line1 fun S b h => ((hP S b).1 h).1, via_line2 fun S b h => ((hC S b).1 h).1,
    via_line3 fun S b h => ((hP S b).1 h).2, via_line4 fun S b h => ((hC S b).1 h).2, via_line5,
    fun S b hb hp hc hpn hcn => ⟨_, subnetVia_ok hb ((hP S b).2 ⟨hp, hpn⟩)
      ((hC S b).2 ⟨hc, hcn⟩)⟩⟩, fun h => ?_⟩
  have hm : subnetVia refNetBuild subnetMsgPortCheck subnetMsgChanCheck mod006_exBadX =
      .error (subnetOnlyMsg "buf") := rfl
  have hb : refNetBuild mod006_exBadX.body = .ok mod006_exBadX.body.collect :=
    refNetBuild_of_terminals_nil rfl
  rcases h.2.2.2.2.2.2 _ _ hm with
    ⟨e, he, -⟩ | ⟨q, hq, hd, -⟩ | ⟨c, hc, -⟩ | ⟨b, hb', ⟨q, hq, -, hn⟩ | ⟨c, hc, -⟩⟩
  · rw [hb] at he; cases he
  · simp only [mod006_exBadX, List.mem_singleton] at hq
    subst hq
    revert hd; decide
  · simp [mod006_exBadX] at hc
  · simp only [mod006_exBadX, List.mem_singleton] at hq
    subst hq
    exact not_msgNames (ch := 'x') (by decide) (by decide) hn
  · simp [mod006_exBadX] at hc

end Libpetri.Spec
