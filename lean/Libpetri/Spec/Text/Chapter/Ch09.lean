import Libpetri.Spec.Text
import Libpetri.Spec.Text.EXP_001
import Libpetri.Spec.Text.EXP_002
import Libpetri.Spec.Text.EXP_003
import Libpetri.Spec.Text.EXP_004
import Libpetri.Spec.Text.EXP_005
import Libpetri.Spec.Text.EXP_006
import Libpetri.Spec.Text.EXP_007
import Libpetri.Spec.Text.EXP_008
import Libpetri.Spec.Text.EXP_010
import Libpetri.Spec.Text.EXP_011
import Libpetri.Spec.Text.EXP_012
import Libpetri.Spec.Text.EXP_013
import Libpetri.Spec.Text.EXP_014
import Libpetri.Spec.Text.EXP_015
import Libpetri.Spec.Text.EXP_016
import Libpetri.Spec.Text.EXP_017
import Libpetri.Spec.Text.EXP_018

spec_chapter "09-export.md"
  scope "Graph export, formal interchange"
  md r#"# 09 — Export

This document specifies graph export formats for visualization and formal analysis interchange.

---

## Graph Export"#
  req EXP_001
  md r#"---"#
  req EXP_002
  md r#"---"#
  req EXP_003
  md r#"---"#
  req EXP_004
  md r#"---"#
  req EXP_005
  md r#"---"#
  req EXP_006
  md r#"---"#
  req EXP_007
  md r#"---"#
  req EXP_008
  md r#"---

## Formal Analysis Export"#
  req EXP_010
  md r#"---"#
  req EXP_011
  md r#"---

## Visualization Rules — junctions and combined edges

The following requirements specify the *visualization* layer that the mapper applies on top of the raw arc set, so XOR/AND fork structure and reset+output coupling are visible to a reader. They are mandatory for all language implementations so Java/TS/Rust mappers (and their doc generators) produce visually identical diagrams."#
  req EXP_012
  md r#"---"#
  req EXP_013
  md r#"---"#
  req EXP_014
  md r#"---"#
  req EXP_015
  md r#"---"#
  req EXP_016
  md r#"---"#
  req EXP_017
  md r#"---"#
  req EXP_018
