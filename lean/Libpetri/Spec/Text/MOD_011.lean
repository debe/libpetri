import Libpetri.Spec.Text

requirement_text MOD_011
  id "MOD-011"
  title "Instance Handle Map (typed port + channel handles)"
  priority MUST
  kind F
  body r#"A module instance MUST expose typed lookup handles:
1. `port(name, type)` returns the renamed `Place<T>` corresponding to the named port from the original interface.
2. `channel(name)` returns the renamed `Transition` corresponding to the named channel from the original interface.
3. `params()` returns the parameter value supplied at instantiation.
4. `prefix()` returns the prefix string supplied at instantiation.

Java and TypeScript return the renamed `Transition` from `channel(name)`; Rust and Python return its name, which identifies it, since transitions are identified by name. Python's port lookup is `port_place_name(name)`, which returns the renamed place's name, and Python's definitions take no parameters, so its instances have no `params()`.

In an implementation that keeps a run-time token type for each port (Java, Rust), the type `T` requested from `port` MUST match the port's originally declared token type, and a mismatch MUST be reported as an error. TypeScript's `port<T>(name)` takes `T` as an annotation it does not check, and Python's lookup takes no type.

⟦s1|*When* `instantiate` succeeds with prefix `p` and the interface declares a port named `n` that exposes the body place `x`, the instance's port lookup for `n` *shall* return the place `x` renamed under `p`, the place `p/x`.⟧

⟦s2|*When* `instantiate` succeeds with prefix `p` and the interface declares a channel named `n` that exposes the body transition `t`, the instance's channel lookup for `n` *shall* return the renamed transition `p/t`.⟧

⟦s3|*If* the port lookup of an instance is given a name that is not a port of the interface, *then* the lookup *shall* fail.⟧

⟦s4|*If* the channel lookup of an instance is given a name that is not a channel of the interface, *then* the lookup *shall* fail.⟧

⟦s5|*When* `instantiate` succeeds with prefix `p`, the instance's `prefix()` *shall* return `p`.⟧

⟦s6|*Where* an implementation keeps a run-time token type for each port (Java, Rust), *when* a port lookup names a port of the interface and requests the token type the port was declared with, the lookup *shall* return the port's renamed place.⟧

⟦s7|*Where* an implementation keeps a run-time token type for each port (Java, Rust), *if* a port lookup names a port of the interface and requests a token type other than the one the port was declared with, *then* the lookup *shall* fail.⟧

⟦s8|*Where* an implementation keeps a run-time token type for each port (Java, Rust), *if* a port lookup names no port of the interface, *then* the lookup *shall* fail, whatever type it requests.⟧

**Acceptance Criteria:**
1. `port("input", String)` on an instance whose interface declared `input: Input<String>` returns the renamed `Place<String>`.
2. In an implementation that keeps a run-time token type for each port (Java, Rust), `port("input", Integer)` on the same instance is rejected with an error.
3. `channel("attempt")` returns the renamed `Transition` whose original name was `attempt`.
4. Looking up a port or channel name that does not exist in the interface produces an error.
5. In an implementation whose instances carry parameters (Java, TypeScript, Rust), `params()` returns the value passed to `instantiate`.

**Depends on:** [MOD-003], [MOD-005], [MOD-010]
**Test derivation:** Build a subnet with port `input: Input<String>` and channel `attempt`; instantiate with prefix `r1`; verify `port("input", String)` returns the renamed place and `channel("attempt")` returns the renamed transition."#
