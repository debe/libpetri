import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.EVT_014
import Libpetri.Spec.Text.EVT_025

runtime_defect RD_45
  title "Java's `SubnetInstanceInfo` loses the build order of its name sets"
  requirements r#"EVT-014 (AC5: rendering the same event stream twice onto the debug protocol
yields identical output), EVT-025 (the reproducibility paragraph, the debug protocol half)."#
  runtimes r#"Java."#
  defect r#"the `SubnetInstanceInfo` constructor copied its place and transition name sets with
`Set.copyOf` (`java/src/main/java/org/libpetri/debug/DebugResponse.java`), which drops the
`LinkedHashSet` order `buildSubnetInstances` builds, so a `Subscribed` response listed the names
of a subnet instance in an order salted per JVM. It was found with RD-36, whose text names the
same constructor."#
  evidence r#"none; the debug protocol has no model."#
  fix r#"the constructor copies each set into an unmodifiable `LinkedHashSet`, which keeps the
build order and still rejects `null`. Java
`DebugProtocolSubnetTest.subnetInstanceNamesKeepBuildOrder_EVT014_AC5`."#
  status "fixed, unreleased"
