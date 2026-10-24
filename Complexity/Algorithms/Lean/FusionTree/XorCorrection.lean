/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.FusionTree.Correction
public import Complexity.Foundations.Data.Nat.Bitwise.HighestDiff
import Batteries.Data.Nat.Bitwise.Lemmas

/-!
# Correction with one exclusive-or comparison

Compare the two neighboring full keys by their exclusive or with the query, then compute
the highest differing bit only for the chosen key. This avoids two highest-bit computations.
The rank primitives remain mathematical specifications in this module.

## Main definitions

* `xorSketchNeighbor`: select a neighboring key by exclusive-or value.
* `xorCorrectedRank`: arbitrary-query correction with this selection rule.

## Main results

* `xorCorrectedRank_eq_upperRank`: exact inclusive rank for every bounded query.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.FusionTree

open Cslib.BitString

/-- Compare only the two sketch neighbors, using a single full-word exclusive or per key. -/
def xorSketchNeighbor {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) (q : ℕ) : Option (Fin n) :=
  chooseByScore (fun i => keys i ^^^ q)
    (sketchPredecessor w keys q) (sketchSuccessor w keys q)

theorem xorSketchNeighbor_spec {n w q : ℕ} {keys : Fin n → ℕ} {j : Fin n}
    (h : xorSketchNeighbor w keys q = some j) :
    IsSketchNeighbor w keys q j ∧
      ∀ i, IsSketchNeighbor w keys q i → keys j ^^^ q ≤ keys i ^^^ q := by
  obtain ⟨hj, hmin⟩ := chooseByScore_spec (fun i => keys i ^^^ q) h
  exact ⟨(isSketchNeighbor_iff j).mpr hj, fun i hi => hmin i ((isSketchNeighbor_iff i).mp hi)⟩

theorem xorSketchNeighbor_eq_none_iff {n w q : ℕ} {keys : Fin n → ℕ} :
    xorSketchNeighbor w keys q = none ↔ n = 0 := by
  rw [xorSketchNeighbor, chooseByScore_eq_none_iff]
  rw [← chooseByScore_eq_none_iff (fun i => divergenceScore w (keys i) q)]
  exact bestSketchNeighbor_eq_none_iff

private theorem miss_of_xorSketchNeighbor {n w q : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) {j : Fin n}
    (hj : xorSketchNeighbor w keys q = some j) (hmiss : keys j ≠ q) :
    ∀ i, keys i ≠ q := by
  intro i hi
  have hscore := (xorSketchNeighbor_spec hj).2 i (isSketchNeighbor_of_eq hsorted hbound i hi)
  rw [hi, Nat.xor_self] at hscore
  exact hmiss (Nat.xor_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hscore))

private theorem xorSketchNeighbor_highestDiff_le {n w q : ℕ} {keys : Fin n → ℕ}
    (hq : q < 2 ^ w) (hbound : ∀ i, keys i < 2 ^ w) (hmiss : ∀ i, keys i ≠ q)
    {j : Fin n} (hj : xorSketchNeighbor w keys q = some j) (i : Fin n)
    (hi : IsSketchNeighbor w keys q i) :
    highestDiff w (keys j) q ≤ highestDiff w (keys i) q := by
  rw [highestDiff_eq_log2_xor (hbound j) hq (hmiss j),
    highestDiff_eq_log2_xor (hbound i) hq (hmiss i)]
  have hz : keys j ^^^ q ≠ 0 := fun h => hmiss j (Nat.xor_eq_zero_iff.mp h)
  have hl := (Nat.log2_lt hz).mpr
    (((xorSketchNeighbor_spec hj).2 i hi).trans_lt Nat.lt_log2_self)
  omega

/-- Correction using an exclusive-or comparison to select the longest-prefix neighbor.
Exact hits return the initial inclusive rank; misses use the sibling-boundary correction. -/
def xorCorrectedRank {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) (q : ℕ) : ℕ :=
  match xorSketchNeighbor w keys q with
  | none => 0
  | some j => if keys j = q then sketchRank w keys q else boundaryRank w keys q j

/-- Exclusive-or selection gives the true inclusive rank for all bounded queries. This
establishes the selection rule's semantics; RAM execution is proved separately. -/
theorem xorCorrectedRank_eq_upperRank {n w q : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) (hq : q < 2 ^ w) :
    xorCorrectedRank w keys q = upperRank keys q := by
  cases hj : xorSketchNeighbor w keys q with
  | none =>
    have hn := xorSketchNeighbor_eq_none_iff.mp hj
    subst n
    simp [xorCorrectedRank, hj, upperRank]
  | some j =>
    rw [xorCorrectedRank, hj]
    dsimp only
    by_cases hhit : keys j = q
    · rw [ite_eq_left hhit]
      unfold sketchRank
      rw [← hhit]
      exact upperRank_sketch_apply hsorted hbound j
    · rw [ite_eq_right hhit]
      have hmiss := miss_of_xorSketchNeighbor hsorted hbound hj hhit
      exact boundaryRank_eq_upperRank hsorted hbound hq hmiss j
        (fun i hi => xorSketchNeighbor_highestDiff_le hq hbound hmiss hj i hi)

end Cslib.Algorithms.Lean.FusionTree
