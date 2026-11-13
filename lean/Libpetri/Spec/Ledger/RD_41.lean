import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.MOD_030
import Libpetri.Spec.Text.MOD_030

runtime_defect RD_41
  title "TypeScript gives an unnamed transition of an instance the action of the first transition of its name"
  requirements r#"MOD-030 (`MOD_030` line 4: a transition the mapping does not name keeps the
action it carried in the receiver)."#
  runtimes r#"TypeScript."#
  defect r#"`Instance.bindActions` binds the renamed body through a resolver that, for a name
the mapping does not give, returns the action of the first transition of the renamed body with
that name (`typescript/src/core/instance.ts`), and
`PetriNet.bindActionsWithResolver` rebuilds a transition whenever the resolver's action differs
from its own (`typescript/src/core/petri-net.ts`). No builder and no instantiation checks
transition names (ruling D23 assumes them distinct; `renameNet` adds every body transition,
`typescript/src/core/internal/subnet-rewriter.ts`), so an instance can hold two
transitions of one name. Instantiate a body with `x` (action A1), `x` (action A2) and `y` as
`p` and call `bindActions({y: B})`: the second `p/x` ends up with A1 instead of A2. With
distinct names the first transition of a name is the transition itself and nothing changes.
Rust and Python (the resolver returns `None`, so the transition is cloned,
`bind_actions_with_resolver` in `rust/libpetri-core/src/petri_net.rs`) and Java (the resolver
returns `null`, so the action is kept, `Instance.bindActions` in
`java/src/main/java/org/libpetri/core/Instance.java`) keep the
transition's own action. The fix is a resolver that returns `null` for a name the mapping does not give, as Java does."#
  evidence r#"⟪MOD_030_forbids_firstOfName⟫ (`MOD_030.lean`): the binding that gives an
unnamed transition the action of the first transition of its name breaks ⟪MOD_030⟫ line 4 on
an instance with two transitions named `p/x`."#
  fix r#"the resolver returns `null` for a name the mapping does not give, so every such
transition keeps its own action. TypeScript `instantiate.test.ts`, "MOD-030: a transition the
mapping does not name keeps its own action, even with a same-named sibling"."#
  status "fixed, unreleased"
