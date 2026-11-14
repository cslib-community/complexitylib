/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Layered
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Tactic.EncLen

/-!
# Encoded sizes of layered Boolean circuits

The node encoding charges two tag bits, both binary reference positions, and all pair framing.
A valid node reading a row of width `w` needs at most `10 + 3 * (log₂ w + 1)` bits. Applying the
list framing twice gives an explicit bound for a well-formed schedule whose input and every
layer have width at most `w`. The bounds include zero-width rows and constant nodes.

## Main results

* `Cslib.Circuits.Boolean.Layered.length_encNode`: exact size in terms of both reference words.
* `Cslib.Circuits.Boolean.Layered.length_encNode_le`: logarithmic size for a valid node.
* `Cslib.Circuits.Boolean.Layered.WellFormed.length_encList_le`: the complete schedule encoding.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

public section

namespace Cslib.Circuits.Boolean.Layered

open Turing.MultiTapeTM

/-- Exact node length: tags and framing cost ten bits; the first binary reference is framed. -/
theorem length_encNode (node : Node) :
    (encNode node).length =
      10 + 2 * (encNat node.code.2.1).length + (encNat node.code.2.2).length := by
  change (encPair (encPair encBool encBool) (encPair encNat encNat) node.code).length = _
  enc_len [List.length_singleton]

/-- Valid references have logarithmic binary encodings; the bound also covers constants. -/
theorem length_encNode_le {node : Node} {width : ℕ} (h : node.Valid width) :
    (encNode node).length ≤ 10 + 3 * (Nat.log2 width + 1) := by
  have hfirst : node.code.2.1 ≤ width := by
    cases node <;> simp only [Node.Valid, Node.code] at h ⊢ <;> omega
  have hsecond : node.code.2.2 ≤ width := by
    cases node <;> simp only [Node.Valid, Node.code] at h ⊢ <;> omega
  have hleft := length_encNat_le_log2 hfirst
  have hright := length_encNat_le_log2 hsecond
  rw [length_encNode]
  omega

/-- A well-formed schedule of bounded width has bounded complete encoding, including every
node delimiter and every layer delimiter. The initial input width is bounded separately. -/
theorem WellFormed.length_encList_le {inputCount width : ℕ} {layers : List (List Node)}
    (h : WellFormed inputCount layers) (hinput : inputCount ≤ width)
    (hlayers : ∀ layer ∈ layers, layer.length ≤ width) :
    (encList (encList encNode) layers).length ≤
      layers.length * (2 * width * (6 * (Nat.log2 width + 1) + 21) + 1) := by
  induction layers generalizing inputCount with
  | nil => simp
  | cons layer layers ih =>
    have hwidth := hlayers layer (List.mem_cons_self ..)
    have hnodes : ∀ node ∈ layer,
        (encNode node).length ≤ 10 + 3 * (Nat.log2 width + 1) := by
      intro node hnode
      apply length_encNode_le
      have hvalid := h.1 node hnode
      cases node <;> simp only [Node.Valid] at hvalid ⊢ <;> omega
    have hhead := Turing.MultiTapeTM.length_encList_le encNode layer hnodes
    have htail := ih h.2 hwidth (fun l hl => hlayers l (List.mem_cons_of_mem _ hl))
    have hhead' : (encList encNode layer).length ≤
        width * (6 * (Nat.log2 width + 1) + 21) := by
      calc
        _ ≤ layer.length * (2 * (10 + 3 * (Nat.log2 width + 1)) + 1) := hhead
        _ ≤ width * (2 * (10 + 3 * (Nat.log2 width + 1)) + 1) := by gcongr
        _ = _ := by ring
    simp only [encList_cons, List.length_append, length_frame, List.length_cons]
    nlinarith

end Cslib.Circuits.Boolean.Layered
