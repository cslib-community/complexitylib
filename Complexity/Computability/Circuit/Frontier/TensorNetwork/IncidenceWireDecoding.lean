/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntry
import Mathlib.Data.List.GetD

/-!
# Both endpoints decode the same physical incidence wires

Prove the actual sequential block reader recovers the little-endian index on every physical
wire block. Row and column port orderings differ, but their common pair index agrees, including
zero-width blocks and words shorter than the declared network. This is the shared-wire step of
[OpenAI2026ETH], Lemma D.2, PDF pp.55–56; global assignment coverage and incidence-polynomial
factorization remain separate obligations.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.wireIndex`: read one actual physical block.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.blockIndices_chunks`: the actual fold reads the
  concatenation of correctly sized chunks without omitting any block.
* `Cslib.Circuits.Frontier.IncidenceNetwork.blockIndices_rowPorts`: actual row decoding.
* `Cslib.Circuits.Frontier.IncidenceNetwork.blockIndices_colPorts`: actual column decoding.
* `Cslib.Circuits.Frontier.IncidenceNetwork.row_col_index_eq`: both endpoints read the same rank.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp.55–56.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.BitString DescribedNetwork

private theorem readChunks {α : Type*} (keys : List α) (block : α → Block)
    (chunk : α → List Bool) (hlen : ∀ a ∈ keys, (chunk a).length = blockWires (block a))
    (rest : List Bool) (acc : List ℕ) :
    ((keys.map block).foldl indexStep (keys.flatMap chunk ++ rest, acc)) =
      (rest, acc ++ keys.map (fun a => lsbValue (chunk a))) := by
  induction keys generalizing acc with
  | nil => simp
  | cons a keys ih =>
    have ha := hlen a List.mem_cons_self
    have ht := fun b hb => hlen b (List.mem_cons_of_mem a hb)
    simp only [List.map_cons, List.flatMap_cons, List.foldl_cons, List.append_assoc]
    have hstep : indexStep (chunk a ++ (keys.flatMap chunk ++ rest), acc) (block a) =
        (keys.flatMap chunk ++ rest, acc ++ [lsbValue (chunk a)]) := by
      simp [indexStep, ← ha]
    rw [hstep, ih ht]
    simp [List.append_assoc]

/-- The actual fold reads each correctly sized chunk, with no positivity assumption on widths. -/
theorem blockIndices_chunks {α : Type*} (keys : List α) (block : α → Block)
    (chunk : α → List Bool) (hlen : ∀ a ∈ keys, (chunk a).length = blockWires (block a)) :
    blockIndices (keys.map block) (keys.flatMap chunk) =
      keys.map (fun a => lsbValue (chunk a)) := by
  have h := congrArg Prod.snd (readChunks keys block chunk hlen [] [])
  simpa only [List.append_nil, List.nil_append, blockIndices] using h

/-- The integer on a physical group-pair wire block, read in little-endian order. -/
@[expose] def wireIndex (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (word : List Bool) (g h : ℕ) : ℕ :=
  lsbValue (wordBits word (List.blockRange (blockWidth J sys d) (g * J + h)))

/-- Actual row decoding reads the physical `(g,h)` blocks in increasing `h` order. -/
theorem blockIndices_rowPorts (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (word : List Bool) (g : ℕ) :
    blockIndices (rowBlocks J sys d g) (wordBits word (rowPorts J sys d g)) =
      (List.range J).map (wireIndex J sys d word g) := by
  unfold rowBlocks rowPorts wordBits
  rw [List.map_flatMap]
  apply blockIndices_chunks
  intro h hh
  simp only [List.length_map, List.blockRange, List.length_range']
  rw [blockWidth_mul_add (List.mem_range.mp hh)]
  rfl

/-- Actual column decoding reads the same physical `(g,h)` blocks in increasing `g` order. -/
theorem blockIndices_colPorts (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (word : List Bool) (h : ℕ) (hh : h < J) :
    blockIndices (colBlocks J sys d h) (wordBits word (colPorts J sys d h)) =
      (List.range J).map (fun g => wireIndex J sys d word g h) := by
  unfold colBlocks colPorts wordBits
  rw [List.map_flatMap]
  apply blockIndices_chunks
  intro g _
  simp only [List.length_map, List.blockRange, List.length_range']
  rw [blockWidth_mul_add hh]
  rfl

/-- A shared group-pair edge block yields identical ranks at both actual endpoints. -/
theorem row_col_index_eq (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (word : List Bool) (g h : ℕ) (hg : g < J) (hh : h < J) :
    (blockIndices (rowBlocks J sys d g) (wordBits word (rowPorts J sys d g))).getD h 0 =
      (blockIndices (colBlocks J sys d h) (wordBits word (colPorts J sys d h))).getD g 0 := by
  rw [blockIndices_rowPorts, blockIndices_colPorts J sys d word h hh,
    List.getD_eq_getElem _ _ (by simpa using hh),
    List.getD_eq_getElem _ _ (by simpa using hg)]
  simp

end Cslib.Circuits.Frontier.IncidenceNetwork
