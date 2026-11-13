import Libpetri.Spec.Text

requirement_text CORE_002
  id "CORE-002"
  title "Place Identity"
  priority MUST
  kind F
  body r#"Two places are the same place exactly when they have the same identity, and an implementation takes a place's identity from its name, or from its name and its token type. It does so the same way throughout the implementation, and never from the object that represents the place. TypeScript, Rust and Python identify a place by its name. Java identifies a place by its name and its token type; a Java place records its token type as a run-time class, so the type arguments of a generic type are not part of it. In TypeScript and Python the language's own equality of place objects is not this identity: two place objects created separately with one name are two objects and one place.

⟦s1|Two places that are the same place *shall* have the same name.⟧

⟦s2|Two places with the same name and the same token type *shall* be the same place.⟧

⟦s3|An implementation *shall* identify a place either by its name, so that two places with the same name are the same place, or by its name and its token type, so that two places that are the same place have the same token type.⟧

**Acceptance Criteria:**
1. A place is the same place as itself.
2. Two independently constructed places with different names are never the same place.
3. Place identity is stable across the lifetime of a net.

**Note:** The naming convention used by modular composition (`prefix/originalName` per [MOD-010]) means that the *same* logical body place, instantiated under two different prefixes, yields two distinct places by this identity rule, which is exactly what per-instance state isolation per [MOD-012] requires.

**Test derivation:** Create two places with different names; verify they are different places. Create one place and reference it twice; verify it is the same place. Create two places separately with the same name and token type and build a net whose transitions use both; verify the engine treats them as one place (the compiled net holds one place of that name). Create two places with the same name and different token types; verify the engine treats them as one place in TypeScript, Rust and Python and as two places in Java."#
