/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Foundations.Data.BitString.Weight
public import Mathlib.Data.List.FinRange

/-!
# The positions of the ones of a bit string

`Cslib.BitString.positions x` lists the coordinates where `x : BitString n` is `true`, in increasing
order and without repetition. Streaming reductions from set disjointness read a bit string as the
stream of its positions.

## Main definitions

* `Cslib.BitString.positions`: the coordinates of the ones of a bit string, as a list.

## Main results

* `Cslib.BitString.mem_positions`, `Cslib.BitString.nodup_positions`,
  `Cslib.BitString.length_positions_le`: membership, no repetition, and length at most `n`.
* `Cslib.BitString.length_positions`: the length of `positions x` equals `weight x`.
* `Cslib.BitString.pairwise_positions`: `positions x` is strictly increasing under `<`.
-/

public section

namespace Cslib.BitString

/-- The coordinates where a bit string is `true`, in increasing order. -/
@[expose] def positions {n : ℕ} (x : BitString n) : List (Fin n) :=
  (List.finRange n).filter fun i => x i

@[simp] theorem mem_positions {n : ℕ} {x : BitString n} {i : Fin n} :
    i ∈ positions x ↔ x i = true := by
  simp [positions, List.mem_finRange]

theorem nodup_positions {n : ℕ} (x : BitString n) : (positions x).Nodup :=
  (List.nodup_finRange n).filter _

theorem length_positions_le {n : ℕ} (x : BitString n) : (positions x).length ≤ n := by
  have h := List.length_filter_le (fun i : Fin n => x i) (List.finRange n)
  rwa [List.length_finRange] at h

/-- The number of 1-bit positions in `x` equals its Hamming weight. -/
@[simp] theorem length_positions {n : ℕ} (x : BitString n) : (positions x).length = weight x := by
  have hnodup : (positions x).Nodup := nodup_positions x
  rw [← List.toFinset_card_of_nodup hnodup]
  dsimp [weight]
  congr 1
  ext i
  simp only [List.mem_toFinset, mem_positions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The positions of 1-bits in `x` are strictly increasing under `<`. -/
theorem pairwise_positions {n : ℕ} (x : BitString n) : (positions x).Pairwise (· < ·) := by
  have hp : (List.finRange n).Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro i hi j hj hij
    simp only [List.getElem_finRange]
    exact hij
  dsimp [positions]
  exact hp.filter _

end Cslib.BitString
