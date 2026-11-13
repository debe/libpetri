import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExport
import Libpetri.Reference.Export
import Libpetri.Reference.ExportCluster
import Libpetri.Spec.Text.EXP_007

set_option linter.missingDocs true

/-!
# EXP-007: Export configuration (`spec/09-export.md`)

Two blocks, as the export design splits the ID.

* `EXP_007_label` is a predicate over an abstract transition labeller `TL : TransLabeller`
  (glossary `GlossaryExport.lean`): the label of a transition node, from the configuration, the
  transition's name, its timing ([TIME-001]) and its priority. Ruling D41 (a) pins the format
  every mapper draws (`transition_label` in the Rust crate `libpetri-export`, module `mapper`,
  `transitionLabel` in `PetriNetGraphMapper.java` and `petri-net-mapper.ts`). The four lines
  determine the label for every configuration (`EXP_007_label_determined`).
* `EXP_007_config` is a predicate over an abstract exporter `E : Exporter`: the drawing has the
  configured layout direction, the show-types option changes nothing (ruling D41 (a)), and two
  configurations that differ only in the direction and the show options give the same graph
  except for its direction and the label inside each transition node: the same edges, clusters
  and `compound` attribute, and the same nodes once the inner transition labels are blanked.

The witnesses are `refTransLabel` (`Reference/Export.lean`) and the clustered exporter
`refExport` (`Reference/ExportCluster.lean`). The config block is proved for every cluster stage
(`EXP_007_config_any`), so the flat exporter `refExportFlat` meets it too. The two blocks are
tied to one mapper by `ExportAgrees`, whose second clause says every transition node carries the
labeller's label.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export
open Libpetri.Novel.TimedScg (Timing)

/-! ## EXP-007, the transition label -/

requirement EXP_007_label
  id "EXP-007"
  title "Export Configuration, the transition label"
  kind F
  scope "every exporter, the label of a transition node"
  source verbatim "spec/09-export.md"
  covers EXP_007.s3, EXP_007.s4, EXP_007.s5, EXP_007.s6, EXP_007.s7, EXP_007.s8
  reading "For the transition labeller TL of an export, every configuration cfg, transition name, timing τ and priority n:"
          "with timing and priority hidden, the label is the name;"
          "with timing shown and priority hidden, the label is the name, then ' [e, l]ms' with e = earliest τ, and l = latest τ when τ has a deadline, else ∞;"
          "when n is 0, the label is the label under cfg with priority hidden;"
          "with priority shown and n not 0, the label is the label under cfg with priority hidden, then ' prio=n'."
  assumes "The model is a transition labeller TL : TransLabeller (glossary): the label of a transition node from the export configuration (glossary ExportCfg), the transition's name, its timing (the Timing of TIME-001: earliest, latest, hasDeadline, in whole milliseconds) and its priority. That every transition node of a drawn graph carries this label is the second clause of ExportAgrees, which the export consistency theorem takes; that the label starts with the name is EXP-003's line. ExportAgrees constrains only nets with X.Distinct (distinct transition names, at most one input arc per place), so the four sentences reach the drawing of such nets only; on a net with two transitions of one name the label of each node is left open, as in the other export blocks (the W4 shape)."
          "The four lines determine the label for every configuration: EXP_007_label_determined shows that refTransLabel is the only labeller that meets the block. So the show-types option, the layout direction, the environment places and the cluster source never change a transition label. This is the label half of the show-types sentence of the config block (ruling D41 (a)); a labeller that reads show-types as a master switch for the whole label violates line 2 (EXP_007_forbids_typesMaster)."
          "Numbers are written as Lean's toString writes Nat and Int: decimal digits, a minus sign before a negative priority (t [7, ∞]ms prio=-1), and ∞ is U+221E. A timing without a deadline is labelled with ∞ and never with its latest() value MAX_DURATION_MS (rulings D2 and D11: the label reads hasDeadline by timing variant); a mapper that prints the maximum is killed (EXP_007_forbids_printsMax). Java's Unconstrained timing, which the Lean Timing lacks, has earliest 0 and no deadline, so the same sentence labels it [0, ∞]ms. Sub-millisecond durations are out of scope: the model's durations are whole milliseconds, Java prints toMillis() and TypeScript the raw number."
          "The parts are in the order name, interval, priority, each after one space; a mapper that writes the priority before the interval violates line 4 (EXP_007_forbids_prioFirst). A mapper that ignores the hide-timing option violates line 1 (EXP_007_forbids_alwaysInterval), and one that writes prio=0 violates line 3 (EXP_007_forbids_prioZero)."
          "AC1 (configuration controls what information is displayed) is these four lines for the transition label, and line 1 and line 3 of the config block for the rest of the drawing. AC2 (default configuration shows all information) is lines 2 and 4 at the default configuration: the interval of every transition, Immediate included as [0, ∞]ms, and the priority when it is not 0 (EXP_007_label_nonvacuous); token types are never drawn (ruling D41 (a)), so they are not part of all information. AC3 (minimal configuration hides timing and priority) is line 1 (export design, skeptic correction S-5): with timing and priority hidden the label is the bare name. The name 'minimal configuration' is kind N: only Java has such a preset (ExportConfig.minimal()), so the block quantifies over configurations instead."
          "The test derivation (export with the default and with the minimal configuration, verify the difference) is EXP_007_label_nonvacuous: t [5, 10]ms prio=3 under the default against t when timing and priority are hidden."
  signoff "2026-11-13 9c513b8ff7802d44 ai"
  statement : TransLabeller → Prop :=
    fun TL => ∀ (cfg : ExportCfg) (name : String) (τ : Timing) (n : Int),
      (cfg.showIntervals = false → cfg.showPriority = false → TL cfg name τ n = name) ∧
      (cfg.showIntervals = true → cfg.showPriority = false → TL cfg name τ n =
        name ++ " [" ++ toString τ.earliest ++ ", " ++
          (if τ.hasDeadline then toString τ.latest else "∞") ++ "]ms") ∧
      (n = 0 → TL cfg name τ n = TL { cfg with showPriority := false } name τ n) ∧
      (cfg.showPriority = true → n ≠ 0 →
        TL cfg name τ n = TL { cfg with showPriority := false } name τ n ++ " prio=" ++ toString n)

/- The pinned readable form of EXP-007 (label): a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_007_label : TransLabeller → Prop :=
fun TL =>
  ∀ (cfg : ExportCfg) (name : String) (τ : Timing) (n : ℤ),
    (cfg.showIntervals = false → cfg.showPriority = false → TL cfg name τ n = name) ∧
      (cfg.showIntervals = true →
          cfg.showPriority = false →
            TL cfg name τ n =
              (name ++ " [" ++ toString τ.earliest ++ ", " ++
                  if τ.hasDeadline = true then toString τ.latest else "∞") ++
                "]ms") ∧
        (n = 0 →
            TL cfg name τ n =
              TL
                { dir := cfg.dir, showTypes := cfg.showTypes, showIntervals := cfg.showIntervals, showPriority := false,
                  env := cfg.env, cluster := cfg.cluster }
                name τ n) ∧
          (cfg.showPriority = true →
            n ≠ 0 →
              TL cfg name τ n =
                TL
                      { dir := cfg.dir, showTypes := cfg.showTypes, showIntervals := cfg.showIntervals,
                        showPriority := false, env := cfg.env, cluster := cfg.cluster }
                      name τ n ++
                    " prio=" ++
                  toString n)
-/
#guard_msgs in #print EXP_007_label

/-! ### The reference -/

/-- The reference labeller satisfies the label block. -/
@[evidence holds EXP_007_label]
theorem EXP_007_label_reference : EXP_007_label refTransLabel := by
  intro cfg name τ n
  refine ⟨fun hi hp => ?_, fun hi hp => ?_, fun h0 => ?_, fun hp hn => ?_⟩
  · simp [refTransLabel, hi, hp]
  · simp [refTransLabel, hi, hp, String.append_assoc]
  · subst h0; simp [refTransLabel]
  · simp [refTransLabel, hp, hn, String.append_assoc]

/-- **The label block determines the label**: the reference labeller is the only one that meets
it. So the show-types option, the direction, the environment places and the cluster source
change no transition label (ruling D41 (a)). -/
theorem EXP_007_label_determined {TL : TransLabeller} (h : EXP_007_label TL) :
    TL = refTransLabel := by
  funext cfg name τ n
  have hoff : ∀ c : ExportCfg, c.showPriority = false →
      TL c name τ n = refTransLabel c name τ n := by
    intro c hc
    cases hi : c.showIntervals
    · rw [(h c name τ n).1 hi hc, refTransLabel_hidden c name τ n hi hc]
    · rw [(h c name τ n).2.1 hi hc]
      simp [refTransLabel, hi, hc, String.append_assoc]
  cases hp : cfg.showPriority
  · exact hoff cfg hp
  · by_cases h0 : n = 0
    · rw [(h cfg name τ n).2.2.1 h0, hoff _ rfl]
      subst h0
      simp [refTransLabel]
    · rw [(h cfg name τ n).2.2.2 hp h0, hoff _ rfl]
      simp [refTransLabel, hp, h0, String.append_assoc]

/-! ### Wrong labellers, one per line -/

/-- A labeller that ignores the hide-timing option. -/
def exp007AlwaysInterval : TransLabeller := fun cfg name τ n =>
  refTransLabel { cfg with showIntervals := true } name τ n

/-- ✗ Showing the interval with timing hidden violates line 1. -/
@[evidence forbids EXP_007_label]
theorem EXP_007_forbids_alwaysInterval : ¬ EXP_007_label exp007AlwaysInterval := by
  intro h
  have := (h { showIntervals := false, showPriority := false } "t" .immediate 0).1 rfl rfl
  revert this
  decide

/-- A labeller that reads the show-types option as a master switch for the whole label, the
literal reading of "minimal configuration hides types, timing and priority". -/
def exp007TypesMaster : TransLabeller := fun cfg name τ n =>
  if cfg.showTypes then refTransLabel cfg name τ n else name

/-- ✗ Letting show-types hide the interval violates line 2 (ruling D41 (a): the option changes
nothing). -/
@[evidence forbids EXP_007_label]
theorem EXP_007_forbids_typesMaster : ¬ EXP_007_label exp007TypesMaster := by
  intro h
  have := (h { showTypes := false, showPriority := false } "t" (.window 5 10) 0).2.1 rfl rfl
  revert this
  decide

/-- A labeller that prints `latest()` without looking at `hasDeadline()`: an `Immediate`
transition shows `MAX_DURATION_MS` (ruling D11). -/
def exp007PrintsMax : TransLabeller := fun cfg name τ n =>
  name ++
    (if cfg.showIntervals then
      " [" ++ toString τ.earliest ++ ", " ++ toString τ.latest ++ "]ms" else "") ++
    (if cfg.showPriority && n != 0 then " prio=" ++ toString n else "")

/-- ✗ Printing the maximum duration for a timing without a deadline violates line 2. -/
@[evidence forbids EXP_007_label]
theorem EXP_007_forbids_printsMax : ¬ EXP_007_label exp007PrintsMax := by
  intro h
  have := (h { showPriority := false } "t" .immediate 0).2.1 rfl rfl
  revert this
  decide

/-- A labeller that prints `prio=0`. -/
def exp007PrioZero : TransLabeller := fun cfg name τ n =>
  refTransLabel cfg name τ n ++ (if cfg.showPriority && n == 0 then " prio=0" else "")

/-- ✗ Printing a zero priority violates line 3. -/
@[evidence forbids EXP_007_label]
theorem EXP_007_forbids_prioZero : ¬ EXP_007_label exp007PrioZero := by
  intro h
  have := (h {} "t" .immediate 0).2.2.1 rfl
  revert this
  decide

/-- A labeller that writes the priority before the interval. -/
def exp007PrioFirst : TransLabeller := fun cfg name τ n =>
  name ++
    (if cfg.showPriority && n != 0 then " prio=" ++ toString n else "") ++
    (if cfg.showIntervals then
      " [" ++ toString τ.earliest ++ ", " ++
        (if τ.hasDeadline then toString τ.latest else "∞") ++ "]ms" else "")

/-- ✗ The priority before the interval violates line 4. -/
@[evidence forbids EXP_007_label]
theorem EXP_007_forbids_prioFirst : ¬ EXP_007_label exp007PrioFirst := by
  intro h
  have := (h {} "t" (.window 5 10) 3).2.2.2 rfl (by decide)
  revert this
  decide

/-! ### Non-vacuity -/

/-- The labels the reference gives under the default configuration, with timing hidden and
with both hidden: every line bites on these values. -/
@[evidence nonvacuous EXP_007_label]
theorem EXP_007_label_nonvacuous :
    refTransLabel {} "t" .immediate 0 = "t [0, ∞]ms" ∧
    refTransLabel {} "t" (.window 5 10) 3 = "t [5, 10]ms prio=3" ∧
    refTransLabel {} "t" (.delayed 7) (-1) = "t [7, ∞]ms prio=-1" ∧
    refTransLabel { showIntervals := false } "t" (.exact 4) 2 = "t prio=2" ∧
    refTransLabel { showIntervals := false, showPriority := false } "t" (.window 5 10) 3 = "t" := by
  decide

/-! ## EXP-007, the configuration -/

requirement EXP_007_config
  id "EXP-007"
  title "Export Configuration"
  kind F
  scope "every exporter"
  source verbatim "spec/09-export.md"
  covers EXP_007.s1, EXP_007.s2, EXP_007.s9, EXP_007.s10, EXP_007.s11, EXP_007.s12
  reading "For the exporter E, every configuration cfg and every net X:"
          "the drawing E cfg X has the layout direction of cfg;"
          "for every value b, E draws X under cfg with show-types set to b exactly as under cfg;"
          "for every configuration cfg' with the environment places and cluster source of cfg, E cfg X and E cfg' X have the same edges, the same clusters, the same compound attribute, and the same nodes once the label inside each transition node is blanked."
  assumes "The model is an exporter E : Exporter (glossary): the drawn graph (glossary XGraph: layout direction, compound attribute, nodes, edges and clusters) of a configuration and a net. Line 3 compares two configurations that agree on the environment places and the cluster source, which the configuration also carries (EXP-008 and EXP-016 read them), so they differ only in the layout direction and the three show options; they have the same edges, clusters and compound attribute, and their nodes are compared after XNode.eraseTransLabel, which blanks the inner label of a transition node and keeps every other field (identity, category, external label) and every other node. So the graph is compared field by field except for the layout direction, which line 1 fixes per configuration. Lists are compared with their order: no option changes the order in any runtime. What the transition labels are is the label block, joined to E by the second clause of ExportAgrees."
          "Line 2 is the show-types sentence, which is ruling D41 (a): the option stays in the configuration types of all three runtimes (Rust DotConfig.show_types, Java ExportConfig.showTypes, TypeScript DotConfig.showTypes) and no mapper reads it, so the 'Show/hide types' bullet is dropped and the sentence says the option changes nothing. A mapper that lets show-types hide the timing and priority of transition labels meets line 3, which allows label changes, and violates line 2 (EXP_007_forbids_typesHide); a mapper that ignores the direction violates line 1 (EXP_007_forbids_fixedDir); a mapper that also drops the timeout labels of output edges when timing is hidden violates line 3 (EXP_007_forbids_hideTimeoutLabels), and so does one that sets the compound attribute from a show option (EXP_007_forbids_compoundFlag)."
          "The 'etc.' of the layout direction bullet is the four directions every runtime has (glossary RankDir: TB, LR, BT, RL; Rust graph RankDir, Java export.graph.RankDir, TypeScript RankDir); line 1 holds for each. The DOT text is not modelled: that the rankdir attribute of the DOT text carries the typed graph's direction (the renderers' RankDir tables, TB, LR, BT and RL each to itself) is kind Q, checked by the renderer tests."
          "The default sentence states no export behaviour: it describes the configuration type, so an exporter cannot break it and the statement has no line for it. The glossary's default ExportCfg is TB with timing and priority shown (EXP_007_default, which cites the sentence), as are Rust DotConfig::default(), Java ExportConfig.DEFAULT and TypeScript DEFAULT_DOT_CONFIG; that the runtime defaults match the glossary is checked by their tests, not here. What the export does under the default is line 1 and the label block at cfg = {}: the drawing is top to bottom (EXP_007_config_nonvacuous) and transition labels carry the interval and the non-zero priority (EXP_007_label_nonvacuous)."
          "AC1 (configuration controls what information is displayed) is line 1 for the direction and the label block for the transition labels; line 3 says the show options change nothing else in the drawn graph (edges, clusters, compound attribute and every node field but the inner transition label). AC2 (default configuration shows all information) is the default sentence together with line 1 and the label block's lines 2 and 4 at the default. AC3 (minimal configuration hides timing and priority) is the label block's line 1; the preset name is kind N (Java only). The test derivation is EXP_007_config_nonvacuous: the worked net of EXP-013 under the default configuration and with timing and priority hidden, same edges, transition labels RefreshCache [1, 5]ms prio=3 against RefreshCache."
  signoff "2026-11-13 af2399c8d9c410dc ai"
  statement : Exporter → Prop :=
    fun E => ∀ (cfg : ExportCfg) (X : ExportNet),
      (E cfg X).dir = cfg.dir ∧
      (∀ b, E { cfg with showTypes := b } X = E cfg X) ∧
      (∀ cfg' : ExportCfg, cfg.env = cfg'.env → cfg.cluster = cfg'.cluster →
        (E cfg X).edges = (E cfg' X).edges ∧
        (E cfg X).clusters = (E cfg' X).clusters ∧
        (E cfg X).compound = (E cfg' X).compound ∧
        (E cfg X).nodes.map XNode.eraseTransLabel = (E cfg' X).nodes.map XNode.eraseTransLabel)

/- The pinned readable form of EXP-007 (config): a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_007_config : Exporter → Prop :=
fun E =>
  ∀ (cfg : ExportCfg) (X : ExportNet),
    (E cfg X).dir = cfg.dir ∧
      (∀ (b : Bool),
          E
              { dir := cfg.dir, showTypes := b, showIntervals := cfg.showIntervals, showPriority := cfg.showPriority,
                env := cfg.env, cluster := cfg.cluster }
              X =
            E cfg X) ∧
        ∀ (cfg' : ExportCfg),
          cfg.env = cfg'.env →
            cfg.cluster = cfg'.cluster →
              (E cfg X).edges = (E cfg' X).edges ∧
                (E cfg X).clusters = (E cfg' X).clusters ∧
                  (E cfg X).compound = (E cfg' X).compound ∧
                    List.map XNode.eraseTransLabel (E cfg X).nodes = List.map XNode.eraseTransLabel (E cfg' X).nodes
-/
#guard_msgs in #print EXP_007_config

/-! ### The reference -/

/-- The reference exporter meets the config block, whatever its cluster stage. -/
theorem EXP_007_config_any (S : ClusterStage) : EXP_007_config (refExportWith S) := by
  intro cfg X
  exact ⟨rfl, fun b => refExportWith_showTypes S cfg X b,
    fun _ he hc =>
      let h := refExportWith_flags S X he hc
      ⟨h.1, h.2.1, rfl, h.2.2⟩⟩

/-- The clustered reference exporter `refExport` (the witness of the export consistency theorem)
meets EXP-007 (config block) (`EXP_007_config_any` at the reference cluster stage). -/
@[evidence holds EXP_007_config]
theorem EXP_007_config_reference : EXP_007_config refExport := EXP_007_config_any _

/-- The default configuration names the top-to-bottom direction and shows timing and priority:
a fact of the glossary's configuration type, which no exporter can break. -/
@[evidence cites "EXP-007" "The default configuration names the top-to-bottom layout direction and shows timing and priority."]
theorem EXP_007_default :
    (({} : ExportCfg).dir = .TB) ∧ ({} : ExportCfg).showIntervals = true ∧
      ({} : ExportCfg).showPriority = true :=
  ⟨rfl, rfl, rfl⟩

/-! ### Wrong exporters, one per line -/

/-- An exporter that always lays out top to bottom. -/
def exp007FixedDir : Exporter := fun cfg X => { refExportFlat cfg X with dir := .TB }

/-- ✗ Ignoring the configured direction violates line 1. -/
@[evidence forbids EXP_007_config]
theorem EXP_007_forbids_fixedDir : ¬ EXP_007_config exp007FixedDir := by
  intro h
  have := (h { dir := .LR } {}).1
  revert this
  decide

/-- An exporter that hides the timing and priority of transition labels when show-types is
off. -/
def exp007TypesHide : Exporter := fun cfg X =>
  if cfg.showTypes then refExportFlat cfg X
  else refExportFlat { cfg with showIntervals := false, showPriority := false } X

/-- A one-transition net: `t` with output `Timeout(5, a)`. -/
def exp007Net : ExportNet :=
  { trans := [{ core := ⟨"t", [], [], [], []⟩, out := some (.timeout 5 (.place "a")) }] }

/-- ✗ Letting show-types hide parts of the label violates line 2. -/
@[evidence forbids EXP_007_config]
theorem EXP_007_forbids_typesHide : ¬ EXP_007_config exp007TypesHide := by
  intro h
  have := (h {} exp007Net).2.1 false
  revert this
  decide

/-- An exporter that also drops the labels of output edges (the `⏱<n>ms` timeout labels) when
timing is hidden. -/
def exp007HideTimeoutLabels : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  if cfg.showIntervals then g
  else { g with edges := g.edges.map fun e => if e.arc = .output then { e with label := none } else e }

/-- ✗ Letting the hide-timing option change an edge violates line 3. -/
@[evidence forbids EXP_007_config]
theorem EXP_007_forbids_hideTimeoutLabels : ¬ EXP_007_config exp007HideTimeoutLabels := by
  intro h
  have := ((h {} exp007Net).2.2 { showIntervals := false } rfl rfl).1
  revert this
  decide

/-- An exporter that sets the `compound` attribute from the show-timing option. -/
def exp007CompoundFlag : Exporter := fun cfg X => { refExportFlat cfg X with compound := cfg.showIntervals }

/-- ✗ Letting a show option change the `compound` attribute violates line 3. -/
@[evidence forbids EXP_007_config]
theorem EXP_007_forbids_compoundFlag : ¬ EXP_007_config exp007CompoundFlag := by
  intro h
  have := ((h {} exp007Net).2.2 { showIntervals := false } rfl rfl).2.2.1
  revert this
  decide

/-! ### Non-vacuity -/

/-- The worked net of [EXP-013] under the default configuration and with timing and priority
hidden: the edges are the same and not empty, the transition labels differ, and the direction
is the configured one, top to bottom under the default. -/
@[evidence nonvacuous EXP_007_config]
theorem EXP_007_config_nonvacuous :
    (refExportFlat { dir := .LR } exportExNet).dir = .LR ∧
    (refExportFlat {} exportExNet).dir = .TB ∧
    (refExportFlat {} exportExNet).edges.length = 9 ∧
    (refExportFlat {} exportExNet).edges =
      (refExportFlat { showIntervals := false, showPriority := false } exportExNet).edges ∧
    ((refExportFlat {} exportExNet).nodes.filterMap fun n =>
        match n.ref with | .trans _ => some n.label | _ => none) =
      ["Try [0, ∞]ms", "RefreshCache [1, 5]ms prio=3"] ∧
    ((refExportFlat { showIntervals := false, showPriority := false } exportExNet).nodes.filterMap
        fun n => match n.ref with | .trans _ => some n.label | _ => none) =
      ["Try", "RefreshCache"] := by
  decide

end Libpetri.Spec
