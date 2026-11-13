import Libpetri.Spec.Text

requirement_text EXP_013
  id "EXP-013"
  title "Combined reset+output Edge"
  priority MUST
  kind F
  body r##"⟦s1|When a transition has both an output arc and a reset arc to the same place P, the mapper MUST draw every output edge to P as a combined edge, styled as the reset-output category (color `#fd7e14`, style `bold`, penwidth `2.0`, arrowhead `normal`) and labelled `"reset+out"`.⟧ ⟦s2|The standalone output edge to P MUST be suppressed in this case.⟧ ⟦s3|The standalone reset edge to P MUST be suppressed in this case.⟧ ⟦s4|When the output spec names P in more than one leaf (for example `Xor(P, And(P, Q))`), each such leaf gives one combined edge.⟧

⟦s5|If a transition resets place P but does not output to P, the standalone reset edge with label `"reset"` MUST still be emitted (existing behavior preserved).⟧

⟦s6|If a transition outputs to P but does not reset P, the standalone output edge MUST be emitted (existing behavior preserved).⟧

⟦s7|The combination applies regardless of whether the output edge originates at the transition directly or at an XOR/AND junction underneath the transition (per EXP-012).⟧ ⟦s8|When the output is a leaf under a junction, the *junction → P* edge is the one that becomes reset-styled with the `"reset+out"` label.⟧

⟦s9|The combined edge carries the label `"reset+out"` alone and is never dashed: it replaces the branch label, the timeout label and the `ForwardInput` label and dash the leaf edge would carry under [EXP-012].⟧

⟦s10|*Where* the transitions of a net have pairwise distinct names and a transition of the net resets place P, each edge the mapper draws for a `Place` leaf for P or a `ForwardInput` leaf into P of its output spec *shall* be an undashed edge of arc type reset-output, in the reset-output style and labelled `reset+out`, whether it starts at the transition or at a junction node.⟧

⟦s11|*Where* the transitions of a net have pairwise distinct names, a transition of the net resets place P and its output spec has a `Place` leaf for P or a `ForwardInput` leaf into P, the mapper *shall* draw no reset edge from that transition to P.⟧

⟦s12|*Where* the transitions of a net have pairwise distinct names, a transition of the net resets place P and its output spec has no `Place` leaf for P and no `ForwardInput` leaf into P, the mapper *shall* draw one undashed reset edge from the transition to P for each reset arc of the transition on P, in the reset style and labelled `reset`.⟧

⟦s13|*Where* the transitions of a net have pairwise distinct names and a transition of the net does not reset place P, each edge the mapper draws for a `Place` leaf for P or a `ForwardInput` leaf into P of its output spec *shall* be of arc type output, in the output style.⟧

⟦s14|*Where* the transitions of a net have pairwise distinct names, for each transition and place P the mapper *shall* draw exactly as many edges of arc type output or reset-output from the transition and its junction nodes into P as the transition's output spec has `Place` leaves for P and `ForwardInput` leaves into P.⟧

⟦s15|The mapper *shall* draw every edge of arc type reset-output from a transition or one of its junction nodes into a place that transition resets.⟧

**Acceptance Criteria:**
1. Transition with `Out.Place(P)` and `reset(P)` exports one orange-bold edge T→P labelled `"reset+out"`. No black output edge to P. No standalone reset edge labelled `"reset"`.
2. Transition with `Out.Place(P)` and no reset exports one black output edge.
3. Transition with reset(P) and no output to P exports one orange-bold edge labelled `"reset"`.
4. Transition with `Out.Xor(P, Q)` and `reset(P)` exports a junction; junction→P is reset-styled with label `"reset+out"`; junction→Q is plain output style.
5. Java, TypeScript, and Rust mappers produce byte-identical edges for the same input.

**Test derivation:** Build nets covering each acceptance case; assert exactly the expected edges (count, color, label) per language.

**Worked DOT:** for a transition `Try` with `Out.Xor(P_Ok, P_Fail)` and `reset(P_Fail)` plus a transition `RefreshCache` with `Out.Place(P_Cache)` and `reset(P_Cache)`:

```
t_RefreshCache -> p_Cache       [color="#fd7e14", style="bold", arrowhead="normal", label="reset+out", penwidth=2];
t_Try -> j_Try__xor_0           [color="#333333", style="solid", arrowhead="normal"];
j_Try__xor_0 -> p_Ok            [color="#333333", style="solid", arrowhead="normal", label="Ok"];
j_Try__xor_0 -> p_Fail          [color="#fd7e14", style="bold", arrowhead="normal", label="reset+out", penwidth=2];
```

Note that the through-junction case (line 4) is identical in style to the direct case (line 1); only the source node differs."##
