import Libpetri.Spec.Ledger
import Libpetri.Reference.Events
import Libpetri.Spec.Req.EVT_014
import Libpetri.Spec.Text.EVT_014

runtime_defect RD_50
  title "The Rust MarkingSnapshot event carries token counts, not tokens"
  requirements r#"EVT-014 (the snapshot is a map from place name to the place's tokens in FIFO
order)."#
  runtimes r#"Rust, Python."#
  defect r#"`NetEvent::MarkingSnapshot` holds `BTreeMap<Arc<str>, usize>`, a count per place,
so the event cannot carry the tokens."#
  evidence r#"⟪EVT_014_forbids_countsOnly⟫: a snapshot that keeps each place's count and
loses its tokens breaks EVT-014, and keeps its order and place-set lines
(⟪evt014_countsOnly_lines34⟫). No theorem states EVT-014 of the Rust emission ⟪polRust⟫."#
  fix r#"none yet. Carrying tokens changes the shape of a public enum variant, a breaking change
that needs a coordinated major release of the Rust crate and the Python binding."#
  status "open"
