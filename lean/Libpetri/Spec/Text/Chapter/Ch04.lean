import Libpetri.Spec.Text
import Libpetri.Spec.Text.EXEC_001
import Libpetri.Spec.Text.EXEC_002
import Libpetri.Spec.Text.EXEC_003
import Libpetri.Spec.Text.EXEC_010
import Libpetri.Spec.Text.EXEC_011
import Libpetri.Spec.Text.EXEC_012
import Libpetri.Spec.Text.EXEC_013
import Libpetri.Spec.Text.EXEC_020
import Libpetri.Spec.Text.EXEC_021
import Libpetri.Spec.Text.EXEC_022
import Libpetri.Spec.Text.EXEC_030
import Libpetri.Spec.Text.EXEC_031
import Libpetri.Spec.Text.EXEC_040
import Libpetri.Spec.Text.EXEC_041
import Libpetri.Spec.Text.EXEC_042
import Libpetri.Spec.Text.EXEC_050

spec_chapter "04-execution-model.md"
  md r#"# 04 — Execution Model

This document specifies the orchestrator loop, scheduling, token consumption, output validation, failure handling, and quiescence detection.

---

## Orchestrator Loop"#
  req EXEC_001
  md r#"---

## Scheduling"#
  req EXEC_002
  md r#"---"#
  req EXEC_003
  md r#"---

## Token Consumption"#
  req EXEC_010
  md r#"---"#
  req EXEC_011
  md r#"---"#
  req EXEC_012
  md r#"---"#
  req EXEC_013
  md r#"---

## Output Handling"#
  req EXEC_020
  md r#"---"#
  req EXEC_021
  md r#"---"#
  req EXEC_022
  md r#"---

## Failure Handling"#
  req EXEC_030
  md r#"---"#
  req EXEC_031
  md r#"---

## Quiescence"#
  req EXEC_040
  md r#"---"#
  req EXEC_041
  md r#"---"#
  req EXEC_042
  md r#"---

## Stale Detection Pattern"#
  req EXEC_050
