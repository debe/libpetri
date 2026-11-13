import Libpetri.Spec.Text

requirement_text EXP_018
  id "EXP-018"
  title "ν-Match Edge Decoration"
  priority SHOULD
  kind F
  body r#"⟦s1|When a transition declares a ν-net join correlation ([NU-020]), each **input
edge** to a correlated place is decorated to mark it as a name-matched input:⟧

- **Color** `#0d9488` (teal, the `match-input` edge style in
  `spec/petri-net-styles.json`), distinguishing it from a plain input edge.
- ⟦s2|**Label** prefixed with the bound-name variable `⟨n⟩` (U+27E8 `n` U+27E9).⟧ ⟦s3|When
  the input also carries a cardinality label ([EXP-006]), the two are joined with
  a single space: `⟨n⟩ ×2`, `⟨n⟩ *`, `⟨n⟩ ≥3`.⟧ ⟦s4|A correlated `One` input shows
  `⟨n⟩` alone.⟧

⟦s5|Non-correlated inputs of the same transition are unaffected.⟧ The decoration is a
mapper concern: it is emitted into the DOT by every exporter, so the canonical
viewer and all three doc generators render it identically with no viewer change.

⟦s6|The export *shall* draw each input arc of a transition as an edge of arc type input from the arc's place to the transition, whether or not the transition correlates the place.⟧

⟦s7|*Where* the match specification of a transition ([NU-020]) correlates the place of one of its input arcs, the export *shall* draw the edge of that arc with the `match-input` style row and label it `⟨n⟩` if the arc's cardinality is `One`, and otherwise `⟨n⟩`, one space and the arc's cardinality label ([EXP-006]).⟧

⟦s8|*Where* a transition does not correlate the place of one of its input arcs, the export *shall* draw the edge of that arc with the `input` style row and give it the arc's cardinality label alone, or no label if the cardinality is `One`.⟧

⟦s9|Apart from ghost edges ([EXP-017]), the export *shall* draw only the input edges of correlated places with the `match-input` style row.⟧

**Acceptance Criteria:**
1. An input edge to a correlated place has color `#0d9488` and a label beginning
   with `⟨n⟩`.
2. A non-correlated input edge on the same transition keeps the default color and
   no `⟨n⟩` prefix.
3. The label combines with cardinality as `⟨n⟩ ×n` / `⟨n⟩ *` / `⟨n⟩ ≥m`.
4. The emitted DOT for a ν-net is byte-identical across the Java, TypeScript, and
   Rust exporters.

**Depends on:** [EXP-006], [EXP-017], [NU-020]
**Test derivation:** Build a join with `match` correlating two `one` inputs;
export; verify both correlated edges are teal and labeled `⟨n⟩`, and a third
non-correlated input is unchanged."#
