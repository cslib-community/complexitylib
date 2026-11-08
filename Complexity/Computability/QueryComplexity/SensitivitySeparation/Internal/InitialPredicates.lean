/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.SensitivitySeparation.Internal.HammingBase
public import Complexity.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveProfiles
public import Complexity.Computability.QueryComplexity.SensitivitySeparation.Internal.Basic

/-!
# Superquadratic sensitivity separation: initial predicates

This file constructs the base case of the recursive construction: the family
`initialFamily d M` of `d + 1` nested predicates on `Fin M × Fin (d + 2)`, where predicate `q`
accepts the inputs within Hamming distance `d - q` of some row center `blockCenter j`. The `M`
rows `baseBlock j` are disjoint sensitive blocks of every predicate at the all-`false` input,
while the sensitivity on rejected inputs is at most `d + 2` and the joint sensitivity is zero.

## Main definitions

* `blockCenter`: the indicator of row `j` of `Fin M × Fin L`.
* `baseBlock`: the set of coordinates in row `j` of `Fin M × Fin L`.
* `initialFamily`: the nested family of unions of Hamming balls around the row centers.

## Main results

* `initialFamily_nested`: `initialFamily d M` is a nested family.
* `initialFamily_zero`: every predicate rejects the all-`false` input.
* `initialFamily_baseBlock`: every predicate accepts the all-`false` input with a row flipped.
* `initialFamily_side_zero`: on rejected inputs the sensitivity is at most `d + 2`.
* `initialFamily_side_one`: on accepted inputs the sensitivity is at most `(d + 2) * M`.
* `initialFamily_joint`: the joint sensitivity of the family is zero.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/InitialPredicates.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- The Boolean input supported on one row of the base coordinate product. -/
def blockCenter {M L : ℕ} (j : Fin M) : Fin M × Fin L → Bool :=
  fun p => decide (p.1 = j)

/-- The coordinates in one row of the base coordinate product. -/
def baseBlock {M L : ℕ} (j : Fin M) : Finset (Fin M × Fin L) :=
  Finset.univ.filter fun p => p.1 = j

/-- A coordinate lies in `baseBlock j` iff its row index is `j`. -/
@[simp] theorem mem_baseBlock {M L : ℕ} (j : Fin M) (p : Fin M × Fin L) :
    p ∈ baseBlock j ↔ p.1 = j := by
  simp [baseBlock]

/-- Each row `baseBlock j` of `Fin M × Fin L` has exactly `L` coordinates. -/
private theorem baseBlock_card {M L : ℕ} (j : Fin M) : (baseBlock (L := L) j).card = L := by
  have h : (baseBlock (L := L) j).card = (Finset.univ : Finset (Fin L)).card := by
    apply Finset.card_bij (fun p _ => p.2)
    · intro p _
      exact Finset.mem_univ _
    · intro p hp q hq hpq
      exact Prod.ext (((mem_baseBlock j p).mp hp).trans ((mem_baseBlock j q).mp hq).symm) hpq
    · intro b _
      exact ⟨(j, b), (mem_baseBlock j (j, b)).mpr rfl, rfl⟩
  simpa using h

/-- For `0 < L`, each row `baseBlock j` is nonempty. -/
theorem baseBlock_nonempty {M L : ℕ} (hL : 0 < L) (j : Fin M) :
    (baseBlock (L := L) j).Nonempty := by
  rw [← Finset.card_pos, baseBlock_card]
  exact hL

/-- Distinct rows `baseBlock i` and `baseBlock j` are disjoint. -/
theorem baseBlock_disjoint {M L : ℕ} :
    Pairwise fun i j : Fin M => Disjoint (baseBlock (L := L) i) (baseBlock j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  rintro ⟨a, b⟩ hi hj
  simp only [mem_baseBlock] at hi hj
  exact hij (hi.symm.trans hj)

/-- Flipping row `j` of the all-`false` input yields `blockCenter j`. -/
private theorem flip_zero_baseBlock {M L : ℕ} (j : Fin M) :
    BitString.flipOn (baseBlock j) (fun _ : Fin M × Fin L => false) = blockCenter j := by
  ext p
  simp [BitString.flipOn_apply, blockCenter]

/-- Each row center `blockCenter j` is at Hamming distance `L` from the all-`false`
input. -/
private theorem hammingDist_zero_blockCenter {M L : ℕ} (j : Fin M) :
    hammingDist (fun _ : Fin M × Fin L => false) (blockCenter j) = L := by
  have hs : (Finset.univ.filter fun p : Fin M × Fin L => false ≠ blockCenter j p) =
      baseBlock j := by
    ext p
    simp [blockCenter]
  rw [hammingDist, hs, baseBlock_card]

/-- Distinct row centers are at Hamming distance `2 * L`. -/
private theorem hammingDist_blockCenter {M L : ℕ} (i j : Fin M) (hij : i ≠ j) :
    hammingDist (blockCenter (L := L) i) (blockCenter j) = 2 * L := by
  have hs : (Finset.univ.filter fun p : Fin M × Fin L =>
      blockCenter i p ≠ blockCenter j p) =
      baseBlock i ∪ baseBlock j := by
    ext ⟨a, b⟩
    by_cases ha : a = i <;> by_cases hb : a = j <;> simp_all [blockCenter]
  rw [hammingDist, hs]
  rw [Finset.card_union_of_disjoint (baseBlock_disjoint hij), baseBlock_card, baseBlock_card]
  omega

/-- Nested unions of Hamming balls around the disjoint row centers. -/
def initialFamily (d M : ℕ) : Fin (d + 1) → (Fin M × Fin (d + 2) → Bool) → Bool :=
  fun q => ballPredicate blockCenter (d - q.val)

/-- `initialFamily d M` is a nested family: the radius `d - q` decreases with `q`, so
acceptance at index `q'` implies acceptance at every index `q ≤ q'`. -/
theorem initialFamily_nested (d M : ℕ) : NestedFamily (initialFamily d M) := by
  constructor
  intro q q' x hqq hx
  exact ballPredicate_nested blockCenter (by omega) x hx

/-- Every predicate of `initialFamily d M` rejects the all-`false` input. -/
theorem initialFamily_zero (d M : ℕ) (q : Fin (d + 1)) :
    initialFamily d M q (fun _ => false) = false := by
  have hn : ¬ ∃ c : Fin M,
      hammingDist (fun _ : Fin M × Fin (d + 2) => false) (blockCenter c) ≤ d - q.val := by
    rintro ⟨c, hc⟩
    rw [hammingDist_zero_blockCenter] at hc
    omega
  simp [initialFamily, ballPredicate, hn]

/-- Every predicate of `initialFamily d M` accepts the all-`false` input with row `j`
flipped. -/
theorem initialFamily_baseBlock (d M : ℕ) (q : Fin (d + 1)) (j : Fin M) :
    initialFamily d M q (BitString.flipOn (baseBlock j) (fun _ => false)) = true := by
  rw [flip_zero_baseBlock]
  apply (ballPredicate_eq_true blockCenter (d - q.val) (blockCenter j)).2
  exact ⟨j, by simp⟩

/-- On rejected inputs, every predicate of `initialFamily d M` has sensitivity at most
`d + 2`. -/
theorem initialFamily_side_zero (d M : ℕ) :
    sideSensitivity (initialFamily d M) false ≤ d + 2 := by
  apply sideSensitivity_le
  intro q x hx
  have hs : ∀ a b : Fin M, a ≠ b →
      2 * ((d - q.val) + 1) < hammingDist (blockCenter (L := d + 2) a) (blockCenter b) := by
    intro a b hab
    rw [hammingDist_blockCenter a b hab]
    omega
  exact (ballPredicate_sensitivityAt_zero_le blockCenter (d - q.val) hs x hx).trans
    (by omega)

/-- On accepted inputs, every predicate of `initialFamily d M` has sensitivity at most
`(d + 2) * M`, the number of coordinates. -/
theorem initialFamily_side_one (d M : ℕ) :
    sideSensitivity (initialFamily d M) true ≤ (d + 2) * M := by
  apply sideSensitivity_le
  intro q x _
  simpa [Nat.mul_comm] using sensitivityAt_le_card (initialFamily d M q) x

/-- For either output bit `b`, the joint sensitivity of `initialFamily d M` is zero: at
an input where predicates `q < q'` both output `b`, no coordinate is sensitive for
both. -/
theorem initialFamily_joint (d M : ℕ) (b : Bool) :
    jointSensitivity (initialFamily d M) b = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply jointSensitivity_le
  intro q q' x hqq hx hx'
  have hrad : d - q'.val < d - q.val := by omega
  unfold jointSensitivityAt
  rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ ⟨hi, hi'⟩
  cases b with
  | false =>
      have hflip : initialFamily d M q' (BitString.flipOn {i} x) = true := by grind
      exact ballPredicate_no_joint_zero blockCenter hrad x i hx hflip
  | true =>
      have hflip : initialFamily d M q (BitString.flipOn {i} x) = false := by grind
      exact ballPredicate_no_joint_one blockCenter hrad x i hx' hflip

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
