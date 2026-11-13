import Libpetri.Spec.Text

requirement_text NU_001
  id "NU-001"
  title "Name Identity"
  priority MUST
  kind F
  body r#"A **name** (`NameId`) is an opaque correlation identity, constructed from an
underlying string value. ⟦s1|Whether a matched transition is enabled, and which tokens
its firing consumes, *shall* depend on the names its keys project only through name
**equality** and, for the tie-break of [NU-020], the name order.⟧ The name order
exists solely for that tie-break and carries no domain meaning.

⟦s2|*When* a matched transition fires with a chosen name, and a one-to-one renaming of
names makes the renamed chosen name the chosen name ([NU-020], [NU-022]) of the same
transition with every name its keys and relay targets project renamed, at the same
marking, that renamed transition *shall* fire from that marking with the renamed
chosen name, for the same emission, delivering the same tokens and leaving the same
marking.⟧

⟦s3|The name constructor *shall* return equal names for equal underlying values and
different names for different underlying values.⟧ ⟦s4|Each implementation *shall* order
names by one fixed strict total order, the name order: if one name precedes another,
the other does not precede it; if a first name precedes a second and the second
precedes a third, the first precedes the third; and of two different names, one
precedes the other.⟧ ⟦s5|Of two names whose underlying values hold only Basic
Multilingual Plane characters, one *shall* precede the other exactly when its value
precedes the other's in the lexicographic order of code points.⟧ On other names the
name order need not agree across implementations: Rust and Python order by code
point, Java and TypeScript by UTF-16 code unit, and the two orders disagree on some
names that hold supplementary-plane characters ([NU-020]).

Identity is a **projection of the token payload**, not a field on the token: a
[NU-020] match (or the analyzer) declares a `value → NameId` key. The token model
([CORE-010]) is unchanged: no name field is added, so event ([EVT-011],
[EVT-012]) and archive formats are unaffected.

**Acceptance Criteria:**
1. Two names constructed from the same underlying value are equal; from
   different values, unequal.
2. Names admit a stable total order consistent across a single implementation.
3. Adding ν-matching to a net does not change the token type or the on-the-wire
   shape of token-bearing events.
4. A one-to-one renaming of the names a join's keys project, which makes the
   renamed chosen name the chosen name of the renamed join, does not change which
   tokens the join consumes or the marking it leaves.

**Test derivation:** Construct `NameId("a")` twice; verify equal. Verify
`NameId("a") < NameId("b")`. Verify a net with no match spec emits identical
token events with and without the ν-net APIs linked. Run a two-branch join on a
marking where two names can join and their earliest tokens differ, then the same
join with its keys composed with a swap of the two names; verify that the renamed
join fires with the renamed name, consumes the same tokens and leaves the same
marking."#
