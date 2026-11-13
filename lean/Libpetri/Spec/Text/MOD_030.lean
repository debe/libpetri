import Libpetri.Spec.Text

requirement_text MOD_030
  id "MOD-030"
  title "Action Binding Per Instance (share-by-default, override via bindActions)"
  priority MUST
  kind F
  body r#"Actions associated with transitions in a subnet definition's body are carried through instantiation **by reference**, not by copy: by default, two instances of the same subnet definition share the same action object for each transition.

A module instance MUST support per-instance action override: `instance.bindActions(mapping)` produces a derived instance whose specified transitions (named by their **original**, pre-prefix names) carry the supplied actions instead of the shared defaults. Transitions not named in the override mapping retain the shared default action.

The override mechanism is per-instance: overriding actions on instance A does NOT affect instance B of the same subnet definition.

**Composition of multiple `bindActions` calls — last-wins replace, not chain.** Each call to `bindActions` returns a derived instance whose action map is the parent instance's action map with the per-transition entries from this call **overwriting** any existing entry for the same transition (entries for transitions not named in the call are inherited unchanged from the parent). Successive `bindActions` calls on the same instance compose left-to-right in derivation order: if `inst1 = inst0.bindActions({"t": A})` and `inst2 = inst1.bindActions({"t": B})`, then `inst2`'s `t` carries action `B`, not a sequential composition of `A` and `B`. A transition therefore carries **exactly one** action at composition time, regardless of how many `bindActions` calls produced the instance. Each `bindActions` call returns a new derived instance and MUST NOT mutate the receiver.

This requirement extends [CORE-042] (action binding separation) into the modular composition layer: subnets remain structure-only by default, with per-instance behavior layered on at composition time.

⟦s1|*When* `bindActions` is called on a module instance with prefix `p` and a mapping in which every key `k` names a transition `p/k` of the instance, the call *shall* return a derived instance.⟧

⟦s2|*When* `bindActions` on a module instance returns a derived instance, the derived instance *shall* have the prefix, the places, the interface and the port and channel handles of the receiver and exactly as many transitions as the receiver, each with the same name, arcs, output specification, timing, priority and declared-to-actual place correspondence ([MOD-031]) as the receiver's transition at the same position.⟧

⟦s3|*When* `bindActions` on a module instance with prefix `p` returns a derived instance and the mapping maps a key `k` to an action, the transition `p/k` *shall* carry that action in the derived instance.⟧

⟦s4|*When* `bindActions` on a module instance with prefix `p` returns a derived instance, a transition whose name is not `p/k` for any key `k` of the mapping *shall* carry in the derived instance the action it carried in the receiver.⟧

⟦s5|Whether a call whose mapping holds a key `k` for which the instance has no transition `p/k` returns a derived instance (Rust, Python: the key is ignored) or is rejected (Java, TypeScript: an error naming the key) is not specified.⟧

**Acceptance Criteria:**
1. By default, two instances of the same subnet definition reference the same action object per transition.
2. `instance.bindActions({"produce": newAction})` produces an instance whose `produce` transition uses `newAction`; the original instance is unchanged.
3. The override map keys use original (un-prefixed) transition names.
4. Transitions not named in the override map retain their shared default action.
5. Action override is purely structural (no runtime state); the override is established before the subnet is composed and fixed for the lifetime of the resulting net.
6. Successive `bindActions` calls compose as last-wins replacement: `inst.bindActions({"t": A}).bindActions({"t": B})` yields an instance whose `t` carries action `B`; action `A` is not invoked at run time for transition `t`.
7. A `bindActions` call that overrides transition `t` leaves the action of any transition `u != t` exactly as inherited from the receiver instance.
8. `bindActions` is non-mutating: invoking it on instance `inst` returns a derived instance; `inst` itself is unchanged and remains usable for subsequent independent derivations.

**Depends on:** [CORE-042], [MOD-010]
**Test derivation:** Instantiate the same subnet twice as `p1`, `p2`. Override `produce` action on `p1`; verify `p1/produce` runs the override action while `p2/produce` runs the default."#
