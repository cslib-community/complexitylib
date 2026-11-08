/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Binary
public import Complexity.Foundations.Data.List.Blocks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

/-!
# Consecutive Boolean blocks and their little-endian ranks

A word on consecutive blocks is equivalent to one rank below `2^(width b)` per block. The
coordinate equivalence uses the actual prefix sums, so this is a correspondence for physical
positions, not a cardinality argument. Width zero and no blocks are included.

## Main definitions

* `Cslib.BitString.blockFinEquiv`: prefix-sum coordinates for the disjoint blocks.
* `Cslib.BitString.blockRankEquiv`: the bijection from words to block ranks.

## Main results

* `Cslib.BitString.blockFinEquiv_apply`: the coordinate is the block start plus its offset.
* `Cslib.BitString.blockRankEquiv_apply`: ranks agree with reading actual consecutive positions.
-/

public section

namespace Cslib.BitString

private theorem sum_width_eq (w : ℕ → ℕ) (B : ℕ) :
    (∑ b : Fin B, w b) = List.blockStart w B := by
  rw [Fin.sum_univ_eq_sum_range]
  exact (List.sum_map_range_eq_sum_range B w).symm

/-- Every physical coordinate has exactly one block and in-block offset. -/
noncomputable def blockFinEquiv (w : ℕ → ℕ) (B : ℕ) :
    (Σ b : Fin B, Fin (w b)) ≃ Fin (List.blockStart w B) :=
  finSigmaFinEquiv.trans (finCongr (sum_width_eq w B))

/-- The equivalence uses the actual consecutive prefix sums, without reordering positions. -/
theorem blockFinEquiv_apply (w : ℕ → ℕ) (B : ℕ) (b : Fin B) (j : Fin (w b)) :
    (blockFinEquiv w B ⟨b, j⟩ : ℕ) = List.blockStart w b + j := by
  change (finSigmaFinEquiv (n := fun b : Fin B => w b) ⟨b, j⟩ : ℕ) = _
  rw [finSigmaFinEquiv_apply]
  congr 1
  simpa only [Fin.val_castLE] using sum_width_eq w b

/-- A Boolean assignment to all wires is equivalent to one full-width binary rank per block. -/
noncomputable def blockRankEquiv (w : ℕ → ℕ) (B : ℕ) :
    (Fin (List.blockStart w B) → Bool) ≃ ((b : Fin B) → Fin (2 ^ w b)) :=
  ((Equiv.piCongrLeft (fun _ => Bool) (blockFinEquiv w B)).symm.trans
    (Equiv.piCurry (fun _ _ => Bool))).trans
      (Equiv.piCongrRight fun b => equivFin (w b))

private theorem blockBits (w : ℕ → ℕ) (B : ℕ)
    (x : Fin (List.blockStart w B) → Bool) (b : Fin B) :
    (List.blockRange w b).map ((List.ofFn x).getD · false) =
      List.ofFn (fun j : Fin (w b) => x (blockFinEquiv w B ⟨b, j⟩)) := by
  apply List.ext_getElem (by simp [List.blockRange])
  intro j hj hj'
  have hb := (blockFinEquiv w B ⟨b, ⟨j, by simpa [List.blockRange] using hj⟩⟩).isLt
  rw [blockFinEquiv_apply] at hb
  simp only [List.blockRange, List.getElem_map, List.getElem_range', one_mul,
    List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_ofFn]
  congr 1
  apply Fin.ext
  exact (blockFinEquiv_apply w B b ⟨j, by simpa using hj'⟩).symm

/-- The rank is exactly the little-endian integer read at the physical block's wire positions. -/
theorem blockRankEquiv_apply (w : ℕ → ℕ) (B : ℕ)
    (x : Fin (List.blockStart w B) → Bool) (b : Fin B) :
    (blockRankEquiv w B x b : ℕ) =
      lsbValue ((List.blockRange w b).map ((List.ofFn x).getD · false)) := by
  rw [blockBits, lsbValue_ofFn]
  rfl

end Cslib.BitString
