import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.CORE_021

runtime_defect RD_07
  title "A Python transition is not equal to itself when read back"
  requirements r#"CORE-021 (AC2)."#
  runtimes r#"Python."#
  defect r#"the `Transition` wrapper defines no `__eq__` or `__hash__`, and `PetriNet.transitions`
returns a fresh wrapper on every access, so `net.transitions[0] == net.transitions[0]` is
`False`. The fix is `__eq__` and `__hash__` on the wrapped `TransitionId`.
`PyTransition` and the `transitions` getter of `PyPetriNet` (`rust/libpetri-py/src/model.rs`)."#
  evidence r#"none; the CORE_021 assumes record it."#
  fix r#"the wrapper defines `__eq__` and `__hash__` over the wrapped transition's `TransitionId`.
Python `test_smoke.py::test_core_021_ac2_transition_read_back_equals_itself`."#
  status "fixed, unreleased"
