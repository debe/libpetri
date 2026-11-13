import Libpetri.Spec.Text

requirement_text MOD_022
  id "MOD-022"
  title "Type Compatibility at Compose"
  priority MUST
  kind B
  body r#"A port binding `port(name, T) -> callerPlace` is well-typed only when the port's declared token type and the caller place's token type are the same `T`. Where the binding is checked depends on the implementation's place identity:

1. In Java, place identity carries the token type. Every compose overload, the map overload with erased generics included, checks the port bindings when `compose` runs, before the collision check of [MOD-020] and before it rewrites anything. It rejects the call at the first binding it meets that names an unknown port or whose caller place has another token type than the port's place. For a binding of another token type the message names the port, the token type of the port's place and the token type of the caller place.
2. In Rust, TypeScript and Python, place identity does not carry the token type, and compose checks no token type. No binding API relates the port's declared token type to the caller place's type. Rust's `bind_port::<T>` and TypeScript's `bindPort<T>` take `T` from the caller place they are given, so a wrong-type binding is no compile-time error there. Python's compose takes a mapping from port names to places. In none of the three is a wrong-type binding rejected at compose. The token type of a caller place is then a property of the caller's place handle, and the typing invariant of [CORE-003] is premised on compatible emissions.

Channel bindings have no token-type check at the channel level (transitions are not typed); arc-level type compatibility falls out from the underlying place token types per [CORE-003].

⟦s1|*Where* place identity carries the token type (Java), *if* a compose call binds no port twice and binds a port to a caller place whose token type differs from the token type of the port's place, *then* the compose call *shall* fail.⟧

⟦s2|*Where* place identity carries the token type (Java), *if* a compose call binds no port twice, binds no channel twice, binds no caller-side transition to two channels, binds only ports of the interface and binds some port to a caller place of another token type, *then* the error message of its failure *shall* name such a port, the token type of the port's place and the token type of the caller place.⟧

⟦s3|*Where* place identity carries the token type (Java), *when* a coherent compose call ([MOD-020]) binds no channel, binds no port twice, binds only ports of the interface, binds each port it binds to a caller place of the token type of the port's place, sends no two different port places that one transition consumes from or that one output branch of a transition names to one caller place, and every transition rewritten through the bindings passes the transition builder's checks, the compose call *shall* succeed.⟧

**Acceptance Criteria:**
1. `port("in", String) -> Place<String>` binding composes successfully.
2. In Java, a `port("in", String) -> Place<Integer>` binding is rejected at compose, through the typed binding overload and the map overload alike, with a message containing `port 'in'`, `String` and `Integer`.

**Depends on:** [CORE-003], [MOD-011], [MOD-020]
**Test derivation:** Java: bind a port to a caller place of another token type, through the typed overload and through the map overload; verify both calls are rejected with a message containing the quoted port name (`port 'in'`, since `in` alone occurs inside other words) and both type names. Every language: bind a port to a caller place of its own token type; verify the composition succeeds."#
