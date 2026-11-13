import Libpetri.Spec.Text
import Libpetri.Spec.Text.IO_001
import Libpetri.Spec.Text.IO_002
import Libpetri.Spec.Text.IO_003
import Libpetri.Spec.Text.IO_004
import Libpetri.Spec.Text.IO_005
import Libpetri.Spec.Text.IO_006
import Libpetri.Spec.Text.IO_007
import Libpetri.Spec.Text.IO_010
import Libpetri.Spec.Text.IO_011
import Libpetri.Spec.Text.IO_012
import Libpetri.Spec.Text.IO_013
import Libpetri.Spec.Text.IO_014
import Libpetri.Spec.Text.IO_015
import Libpetri.Spec.Text.IO_016
import Libpetri.Spec.Text.IO_017

spec_chapter "02-input-output-specs.md"
  scope "Input cardinality, composite output routing, validation"
  md r#"# 02 — Input & Output Specifications

This document specifies input cardinality and composite output routing semantics.

---

## Input Cardinality"#
  req IO_001
  md r#"---"#
  req IO_002
  md r#"---"#
  req IO_003
  md r#"---"#
  req IO_004
  md r#"---"#
  req IO_005
  md r#"---"#
  req IO_006
  md r#"---"#
  req IO_007
  md r#"---

## Output Composition

Building a transition runs the build-time checks of its output spec in this order and fails with the message of the first check that fails: a place named twice in one output branch ([IO-011]), more than one `Timeout` node ([IO-013]), an `Xor` node inside the child of the `Timeout` node ([IO-013]), a `ForwardInput` outside the child of a `Timeout` node ([IO-014]), a `ForwardInput` whose `from` is not an input place ([IO-014] AC3), and two distinct assignments that claim the same set of places ([IO-012]). Every construction path (builders, composition, channel merge, fusion) builds its transitions through these checks, and no executor option skips them ([CONC-026])."#
  req IO_010
  md r#"---"#
  req IO_011
  md r#"---"#
  req IO_012
  md r#"---"#
  req IO_013
  md r#"---"#
  req IO_014
  md r#"---"#
  req IO_015
  md r#"---"#
  req IO_016
  md r#"---"#
  req IO_017
