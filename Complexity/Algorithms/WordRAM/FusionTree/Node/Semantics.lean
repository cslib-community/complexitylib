/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Parameters
public import Complexity.Algorithms.WordRAM.FusionTree.Neighbors
public import Complexity.Algorithms.WordRAM.FusionTree.Boundary
import Batteries.Data.Nat.Bitwise.Lemmas

/-!
# Arithmetic ranks and full-key correction

The arithmetic ranks use natural-number arrays; the correction theorems use `Fin`-indexed
keys. These bridges identify the two counts and justify correction for the concrete
exclusive-or neighbor selection, including exact hits.

## Main results

* `NodeSemantics.upperRank_eq`: the arithmetic count is the inclusive perfect-sketch rank.
* `NodeSemantics.correct`: a minimum-exclusive-or sketch neighbor suffices for full-key rank.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.NodeSemantics

open Cslib.WordRAM Cslib.BitString Lean.FusionTree

private theorem card_filter_range {n : ℕ} (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range n).filter P).card = (Finset.univ.filter fun i : Fin n => P i.val).card := by
  apply Finset.card_bij (fun i hi => (⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩ : Fin n))
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ he
    exact congrArg Fin.val he
  · intro i hi
    exact ⟨i.val, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr i.isLt, (Finset.mem_filter.mp hi).2⟩, rfl⟩

/-- The arithmetic inclusive count agrees with the perfect-sketch rank on every input. -/
theorem upperRank_eq {w n : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (hn : 0 < n) (hs : StrictMono keys) (hk : ∀ i, keys i < 2 ^ w) (q : ℕ) :
    upperRankExpr p.b n p.sketches (p.compressed q) = sketchRank w keys q := by
  rw [p.upperRank_eq hn hs hk, card_filter_range]
  simp only [sketchRank, upperRank, dite_true, Fin.isLt]

/-- The arithmetic strict count agrees with the strict perfect-sketch rank. -/
theorem lowerRank_eq {w n : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (hn : 0 < n) (hs : StrictMono keys) (hk : ∀ i, keys i < 2 ^ w) (q : ℕ) :
    n - countGuards p.b n p.sketches (p.compressed q) =
      lowerRank (fun i => sketch (relevantBits w keys) (keys i))
        (sketch (relevantBits w keys) q) := by
  rw [p.lowerRank_eq hn hs hk, card_filter_range]
  simp only [lowerRank, dite_true, Fin.isLt]

/-- A minimum-exclusive-or neighbor is an exact hit whenever any stored key is a hit. -/
private theorem miss {w n q : ℕ} {keys : Fin n → ℕ} (hs : StrictMono keys)
    (hk : ∀ i, keys i < 2 ^ w) (j : Fin n)
    (hbest : ∀ i, IsSketchNeighbor w keys q i → keys j ^^^ q ≤ keys i ^^^ q)
    (hj : keys j ≠ q) : ∀ i, keys i ≠ q := by
  intro i hi
  have h := hbest i (isSketchNeighbor_of_eq hs hk i hi)
  rw [hi, Nat.xor_self] at h
  exact hj (Nat.xor_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h))

/-- Concrete exclusive-or selection supports the full correction theorem. This statement
does not require identifying an `Option`-valued selection implementation. -/
theorem correct {w n q : ℕ} {keys : Fin n → ℕ} (hs : StrictMono keys)
    (hk : ∀ i, keys i < 2 ^ w) (hq : Fits w q) (j : Fin n)
    (hbest : ∀ i, IsSketchNeighbor w keys q i → keys j ^^^ q ≤ keys i ^^^ q) :
    (if keys j = q then sketchRank w keys q else boundaryRank w keys q j) =
      upperRank keys q := by
  by_cases hj : keys j = q
  · simp only [hj, ↓reduceIte, sketchRank]
    rw [← hj]
    exact upperRank_sketch_apply hs hk j
  · rw [ite_eq_right hj]
    have hm := miss hs hk j hbest hj
    apply boundaryRank_eq_upperRank hs hk hq hm j
    intro i hi
    rw [highestDiff_eq_log2_xor (hk j) hq (hm j),
      highestDiff_eq_log2_xor (hk i) hq (hm i)]
    have hz : keys j ^^^ q ≠ 0 := fun h => hm j (Nat.xor_eq_zero_iff.mp h)
    have hl := (Nat.log2_lt hz).mpr ((hbest i hi).trans_lt Nat.lt_log2_self)
    omega

end Cslib.Algorithms.WordRAM.FusionTree.NodeSemantics
