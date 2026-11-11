/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Privacy.DifferentialPrivacy.Basic
public import Complexity.Probability.Product
public import Mathlib.InformationTheory.Hamming

/-!
# Hamming adjacency and group privacy

Datasets are maps `x : ι → X` assigning a row to each index. Two datasets are Hamming-adjacent
(`HammingAdjacent`) when they differ in at most one row, the neighbor relation of
[GhoshRoughgardenSundararajan2012, §2.1]. For finite `ι` this is `hammingDist x y ≤ 1`
(`hammingAdjacent_iff_hammingDist_le_one`).

Group privacy: a mechanism that is `(ε, δ)`-private for Hamming adjacency is
`(k ε, ∑ i < k, exp (i ε) · δ)`-private for datasets at Hamming distance at most `k`
(`DifferentiallyPrivate.hammingDist_le`). For `δ = 0` this is `(k ε, 0)`
(`DifferentiallyPrivate.hammingDist_le_of_pure`), the Hamming-distance form of
[DworkRoth2014, Theorem 2.2], which is stated for `ℓ₁` distance between histograms; for `0 ≤ ε`
the additive term is at most `k exp ((k - 1) ε) δ` (`DifferentiallyPrivate.hammingDist_le'`), the
bound in the footnote to that theorem. The proof walks along a chain of adjacent datasets.

`DifferentiallyPrivate.pi`: if every respondent applies an `(ε, 0)`-private local randomizer to
their own row independently, the joint mechanism is `(ε, 0)`-private for Hamming adjacency.

## Main definitions

* `Cslib.Privacy.HammingAdjacent`: datasets differing in at most one row.

## Main results

* `Cslib.Privacy.DifferentiallyPrivate.hammingDist_le`,
  `Cslib.Privacy.DifferentiallyPrivate.hammingDist_le_of_pure`,
  `Cslib.Privacy.DifferentiallyPrivate.hammingDist_le'`: group privacy.
* `Cslib.Privacy.DifferentiallyPrivate.pi`: products of local randomizers.

## References

* [DworkRoth2014]
* [GhoshRoughgardenSundararajan2012]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

universe u v

section Hamming

variable {ι : Type*} {X : Type*}

/-- Two datasets are Hamming-adjacent when they differ in at most one row. -/
@[expose] def HammingAdjacent (x y : ι → X) : Prop := {i | x i ≠ y i}.Subsingleton

/-- For finitely many rows, Hamming adjacency is Hamming distance at most one. -/
theorem hammingAdjacent_iff_hammingDist_le_one [Fintype ι] [DecidableEq X] {x y : ι → X} :
    HammingAdjacent x y ↔ hammingDist x y ≤ 1 := by
  classical
  rw [hammingDist, Finset.card_le_one, HammingAdjacent, Set.Subsingleton]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]

/-- Every dataset is Hamming-adjacent to itself. -/
@[refl] theorem HammingAdjacent.refl (x : ι → X) : HammingAdjacent x x := by
  intro i hi; exact absurd rfl hi

/-- Hamming adjacency is symmetric. -/
theorem HammingAdjacent.symm {x y : ι → X} (h : HammingAdjacent x y) : HammingAdjacent y x :=
  fun _ hi _ hj => h (Ne.symm hi) (Ne.symm hj)

/-- Changing one row gives a Hamming-adjacent dataset. -/
theorem hammingAdjacent_update [DecidableEq ι] (x : ι → X) (i : ι) (a : X) :
    HammingAdjacent x (Function.update x i a) := by
  intro j hj k hk
  simp only [Set.mem_ofPred_eq] at hj hk
  by_contra hne
  rcases eq_or_ne j i with rfl | hji
  · rw [Function.update_of_ne (Ne.symm hne)] at hk
    exact hk rfl
  · rw [Function.update_of_ne hji] at hj
    exact hj rfl

/-- A Hamming-adjacent dataset is obtained by changing any row in which it differs. -/
theorem HammingAdjacent.eq_update [DecidableEq ι] {x y : ι → X} (h : HammingAdjacent x y)
    {i : ι} (hi : x i ≠ y i) : y = Function.update x i (y i) := by
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp
  · rw [Function.update_of_ne hji]
    by_contra hj
    exact hji (h (Ne.symm hj) hi)

/-- A pair at Hamming distance at most `k + 1` passes through a dataset at distance at most `k`
from the first and adjacent to the second. -/
theorem exists_hammingDist_le_and_hammingAdjacent [Fintype ι] [DecidableEq X] {k : ℕ}
    {x y : ι → X} (h : hammingDist x y ≤ k + 1) :
    ∃ z, hammingDist x z ≤ k ∧ HammingAdjacent z y := by
  classical
  by_cases hxy : x = y
  · exact ⟨x, by simp [hxy], hxy ▸ HammingAdjacent.refl x⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨Function.update y i (x i), ?_, (hammingAdjacent_update y i (x i)).symm⟩
  have hsub : (Finset.univ.filter fun j => x j ≠ Function.update y i (x i) j) ⊆
      (Finset.univ.filter fun j => x j ≠ y j).erase i := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hj ⊢
    rcases eq_or_ne j i with rfl | hji
    · simp at hj
    · rw [Function.update_of_ne hji] at hj
      exact ⟨hji, hj⟩
  have hmem : i ∈ Finset.univ.filter fun j => x j ≠ y j := by simpa using hi
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem] at this
  unfold hammingDist at h ⊢
  omega

end Hamming

namespace DifferentiallyPrivate

variable {R : Type v} {ι X : Type*} [Fintype ι] [DecidableEq X] {M : (ι → X) → PMF R} {ε : ℝ}
  {δ : ℝ≥0∞}

/-- Group privacy: an `(ε, δ)`-private mechanism for Hamming adjacency is
`(k ε, ∑ i < k, exp (i ε) · δ)`-private for datasets at Hamming distance at most `k`. -/
theorem hammingDist_le (h : DifferentiallyPrivate HammingAdjacent M ε δ) (k : ℕ) :
    DifferentiallyPrivate (fun x y => hammingDist x y ≤ k) M (k * ε)
      (∑ i ∈ Finset.range k, ENNReal.ofReal (Real.exp (i * ε)) * δ) := by
  induction k with
  | zero =>
    intro x y hxy S
    have : x = y := hammingDist_eq_zero.mp (Nat.le_zero.mp hxy)
    subst this
    simp
  | succ k ih =>
    have := (ih.trans h).mono_adj (Adj' := fun x y => hammingDist x y ≤ k + 1)
      fun x y hxy => exists_hammingDist_le_and_hammingAdjacent hxy
    convert this using 1
    · push_cast
      ring
    · rw [Finset.sum_range_succ]

/-- Group privacy for pure privacy: an `(ε, 0)`-private mechanism for Hamming adjacency is
`(k ε, 0)`-private for datasets at Hamming distance at most `k` (the Hamming-distance form of
[DworkRoth2014, Theorem 2.2]). -/
theorem hammingDist_le_of_pure (h : DifferentiallyPrivate HammingAdjacent M ε 0) (k : ℕ) :
    DifferentiallyPrivate (fun x y => hammingDist x y ≤ k) M (k * ε) 0 := by
  simpa using h.hammingDist_le k

/-- Group privacy with the additive term `k exp ((k - 1) ε) δ` of the footnote to
[DworkRoth2014, Theorem 2.2], for `0 ≤ ε`. -/
theorem hammingDist_le' (h : DifferentiallyPrivate HammingAdjacent M ε δ) (hε : 0 ≤ ε) (k : ℕ) :
    DifferentiallyPrivate (fun x y => hammingDist x y ≤ k) M (k * ε)
      (k * ENNReal.ofReal (Real.exp ((k - 1 : ℕ) * ε)) * δ) := by
  refine (h.hammingDist_le k).mono le_rfl ?_
  calc ∑ i ∈ Finset.range k, ENNReal.ofReal (Real.exp (i * ε)) * δ
      ≤ ∑ _i ∈ Finset.range k, ENNReal.ofReal (Real.exp ((k - 1 : ℕ) * ε)) * δ := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ k - 1 := by
          have := Finset.mem_range.mp hi; omega
        gcongr
    _ = k * ENNReal.ofReal (Real.exp ((k - 1 : ℕ) * ε)) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

end DifferentiallyPrivate

/-- Products of local randomizers: if each respondent's randomizer `M i` is `(ε, 0)`-private
against arbitrary changes of its own input, the mechanism applying all of them independently is
`(ε, 0)`-private for Hamming adjacency. -/
theorem DifferentiallyPrivate.pi {ι X Y : Type*} [Fintype ι] [Finite Y]
    {M : ι → X → PMF Y} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i, DifferentiallyPrivate (fun _ _ => True) (M i) ε 0) :
    DifferentiallyPrivate HammingAdjacent (fun x => Probability.PMF.pi fun i => M i (x i)) ε 0 := by
  classical
  refine DifferentiallyPrivate.of_apply_le fun x y hxy r => ?_
  simp only [Probability.PMF.pi_apply]
  by_cases hxy' : x = y
  · subst hxy'
    exact le_mul_of_one_le_left zero_le (by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hε))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy'
  have hrest : ∀ j ∈ Finset.univ.erase i, M j (x j) (r j) = M j (y j) (r j) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have : x j = y j := by
      by_contra hne
      exact hji (hxy hne hi)
    rw [this]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Finset.prod_congr rfl hrest, ← mul_assoc]
  gcongr
  exact DifferentiallyPrivate.iff_apply_le.mp (h i) trivial (r i)

end Cslib.Privacy
