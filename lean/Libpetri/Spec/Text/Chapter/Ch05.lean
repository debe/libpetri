import Libpetri.Spec.Text
import Libpetri.Spec.Text.CONC_001
import Libpetri.Spec.Text.CONC_002
import Libpetri.Spec.Text.CONC_003
import Libpetri.Spec.Text.CONC_004
import Libpetri.Spec.Text.CONC_005
import Libpetri.Spec.Text.CONC_006
import Libpetri.Spec.Text.CONC_007
import Libpetri.Spec.Text.CONC_008
import Libpetri.Spec.Text.CONC_020
import Libpetri.Spec.Text.CONC_021
import Libpetri.Spec.Text.CONC_022
import Libpetri.Spec.Text.CONC_023
import Libpetri.Spec.Text.CONC_024
import Libpetri.Spec.Text.CONC_025
import Libpetri.Spec.Text.CONC_026
import Libpetri.Spec.Text.CONC_010
import Libpetri.Spec.Text.CONC_011
import Libpetri.Spec.Text.CONC_012

spec_chapter "05-concurrency.md"
  scope "Single-threaded orchestrator, bitmap executor, precompiled flat-array executor, async actions, wake-up"
  md r#"# 05 — Concurrency

This document specifies the concurrency model: single-threaded orchestrator, async action dispatch, bitmap executor optimization, precompiled flat-array executor, and wake-up mechanisms.

---

## Single-Threaded Orchestrator"#
  req CONC_001
  md r#"---"#
  req CONC_002
  md r#"---"#
  req CONC_003
  md r#"---

## Bitmap Executor"#
  req CONC_004
  md r#"---"#
  req CONC_005
  md r#"---"#
  req CONC_006
  md r#"---"#
  req CONC_007
  md r#"---"#
  req CONC_008
  md r#"---

## Precompiled Flat-Array Executor"#
  req CONC_020
  md r#"---"#
  req CONC_021
  md r#"---"#
  req CONC_022
  md r#"---"#
  req CONC_023
  md r#"---"#
  req CONC_024
  md r#"---"#
  req CONC_025
  md r#"---"#
  req CONC_026
  md r#"---

## Wake-Up Mechanism"#
  req CONC_010
  md r#"---"#
  req CONC_011
  md r#"---"#
  req CONC_012
