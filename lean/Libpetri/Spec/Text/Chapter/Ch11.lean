import Libpetri.Spec.Text
import Libpetri.Spec.Text.MOD_001
import Libpetri.Spec.Text.MOD_002
import Libpetri.Spec.Text.MOD_003
import Libpetri.Spec.Text.MOD_004
import Libpetri.Spec.Text.MOD_005
import Libpetri.Spec.Text.MOD_006
import Libpetri.Spec.Text.MOD_010
import Libpetri.Spec.Text.MOD_011
import Libpetri.Spec.Text.MOD_012
import Libpetri.Spec.Text.MOD_013
import Libpetri.Spec.Text.MOD_014
import Libpetri.Spec.Text.MOD_020
import Libpetri.Spec.Text.MOD_021
import Libpetri.Spec.Text.MOD_022
import Libpetri.Spec.Text.MOD_023
import Libpetri.Spec.Text.MOD_024
import Libpetri.Spec.Text.MOD_025
import Libpetri.Spec.Text.MOD_026
import Libpetri.Spec.Text.MOD_027
import Libpetri.Spec.Text.MOD_030
import Libpetri.Spec.Text.MOD_031
import Libpetri.Spec.Text.MOD_040
import Libpetri.Spec.Text.MOD_041
import Libpetri.Spec.Text.MOD_050
import Libpetri.Spec.Text.MOD_051
import Libpetri.Spec.Text.MOD_060
import Libpetri.Spec.Text.MOD_061

spec_chapter "11-modular-composition.md"
  md r#"# 11 — Modular Composition

This document specifies the **modular composition** extension of the CTPN engine: open net fragments (subnets) with declared interfaces, instantiation, structural composition by port mapping, synchronous channel fusion of interface transitions, action binding per instance, and orthogonal fusion of N places.

The vocabulary follows the ISO/IEC 15909-2 PNML *modular extension*: an open net is a Petri net augmented with an **interface** consisting of **interface places** (ports) and **interface transitions** (synchronous channels). A **module instance** is a renamed copy of an open net wired into an enclosing net by mapping its interface elements to enclosing-net elements.

Composition is **build-time only**. The runtime, exporter, verifier, and event subsystems see a normal flat `PetriNet` after composition completes. No semantic primitive in this document changes the contract of CORE, EXEC, CONC, EVT, ENV, VER, EXP, or PERF for the resulting flat net.

---

## Subnet Definition"#
  req MOD_001
  md r#"---"#
  req MOD_002
  md r#"---

## Interface Declaration"#
  req MOD_003
  md r#"---"#
  req MOD_004
  md r#"---"#
  req MOD_005
  md r#"---"#
  req MOD_006
  md r#"---

## Instantiation"#
  req MOD_010
  md r#"---"#
  req MOD_011
  md r#"---"#
  req MOD_012
  md r#"---"#
  req MOD_013
  md r#"---"#
  req MOD_014
  md r#"---

## Composition"#
  req MOD_020
  md r#"---"#
  req MOD_021
  md r#"---"#
  req MOD_022
  md r#"---"#
  req MOD_023
  md r#"---"#
  req MOD_024
  md r#"---"#
  req MOD_025
  md r#"---"#
  req MOD_026
  md r#"---"#
  req MOD_027
  md r#"---

## Action Binding"#
  req MOD_030
  md r#"---"#
  req MOD_031
  md r#"---

## Export and Debug"#
  req MOD_040
  md r#"---"#
  req MOD_041
  md r#"---

## Verification"#
  req MOD_050
  md r#"---"#
  req MOD_051
  md r#"---

## Fusion (orthogonal to composition)"#
  req MOD_060
  md r#"---"#
  req MOD_061
