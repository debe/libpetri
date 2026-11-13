import Libpetri.Spec.Text

requirement_text CONC_021
  id "CONC-021"
  title "Opcode-Based Consume Operations"
  priority SHOULD
  kind F
  body r#"Each transition's input and reset arcs are compiled into a flat integer array of opcodes. During firing, the executor iterates the opcode array instead of pattern-matching on sealed arc types, except for a transition with a match specification, whose inputs are consumed through the match path (its correlated inputs by name, [NU-020]). Read arcs are compiled into a separate place-ID array.

Opcodes:
- `CONSUME_ONE(0) placeId`: consume one token from place
- `CONSUME_N(1) placeId count`: consume exactly N tokens
- `CONSUME_ALL(2) placeId`: consume all tokens the firing may drain ([EXEC-003] AC5)
- `CONSUME_ATLEAST(3) placeId minimum`: consume at least N tokens (takes all tokens the firing may drain, [EXEC-003] AC5)
- `RESET(4) placeId`: clear from the place all tokens the firing may drain ([EXEC-003] AC5)

⟦s1|*When* the precompiled executor fires a transition that has no match specification ([NU-020]), its consume operations *shall* hand the action from each input place the oldest tokens the place holds, as many as the consumption count of the input arc ([IO-007]) for the number of tokens the firing may drain ([EXEC-003] AC5), in queue order, and nothing from any other place.⟧

⟦s2|*When* the precompiled executor fires a transition that has no match specification ([NU-020]), its consume operations *shall* hand the action for each read arc the head of the read place's queue as it is after the input operations and before the reset operations.⟧

⟦s3|*When* the precompiled executor fires a transition that has no match specification ([NU-020]), its consume operations *shall* remove from each reset place every token the firing may drain ([EXEC-003] AC5), leave each other input place its queue without the tokens handed to the action, leave the queue of every other place unchanged, and hold a queue for every place the token storage held and for no other place.⟧

**Acceptance Criteria:**
1. Each transition has a precompiled consume operation array.
2. Read arcs are compiled into a separate place-ID array (reads do not consume).
3. Firing a transition iterates the opcode array without type dispatch, except for a transition with a match specification, whose inputs are consumed through the match path (its correlated inputs by name, [NU-020]).
4. All five opcodes produce the same observable behavior as the corresponding arc types.

**Test derivation:** Compile a net with all arc types; fire transitions; verify token consumption matches bitmap executor."#
