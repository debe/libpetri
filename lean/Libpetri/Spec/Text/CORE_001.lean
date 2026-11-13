import Libpetri.Spec.Text

requirement_text CORE_001
  id "CORE-001"
  title "Place Definition"
  priority MUST
  kind Q
  body r#"A place is a named, typed container that holds tokens. Each place has a string name and an associated token value type.

**Acceptance Criteria:**
1. A place can be created with a name and a token type.
2. The name is available for display, debugging, and export.

**Note:** When a place is part of a subnet body composed into an enclosing net, its observable name is rewritten by prefix concatenation per [MOD-010] (separator `/`). The naming rule is owned by MOD; CORE only requires that *some* string name exists and is stable.

**Test derivation:** Create a place with name "Ready" and token type String; verify name and type are retrievable."#
