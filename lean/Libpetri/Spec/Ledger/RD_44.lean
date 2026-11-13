import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.EVT_025

runtime_defect RD_44
  title "Python archive headers carry an empty structure"
  requirements r#"EVT-025 (the writer line: the header carries the session's own header fields)."#
  runtimes r#"Python."#
  defect r#"`write_from_store` built the archived debug session with `places: None`
(`rust/libpetri-py/src/archive.rs`), so `build_net_structure` returned no places and no
transitions (`rust/libpetri-debug/src/debug_session_registry.rs`) and the header's
`structure` listed neither, although the writer has the net. The Rust registry fills it (`places:
Some(PlaceAnalysis::from_net(net))`, `register_with_tags` in `debug_session_registry.rs`)."#
  evidence r#"none; the EVT_025 model keeps the session's header fields, the net structure
among them, opaque."#
  fix r#"the archived session carries `places: Some(PlaceAnalysis::from_net(net))`, so the
header's `structure` lists the net's places and transitions. Python
`test_archive.py::test_evt_025_archive_header_structure_lists_the_nets_places_and_transitions`."#
  status "fixed, unreleased"
