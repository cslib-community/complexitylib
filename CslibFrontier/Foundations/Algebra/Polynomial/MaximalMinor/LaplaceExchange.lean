/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.MaximalMinor.GenericMinorBasic

/-!
# The permutation form of generalized Laplace exchange

We first prove the combinatorial exchange identity for the permutation
expansion of a Laplace product.  The later determinant file identifies this
permutation sum with the signed product of complementary minors.  Keeping the
two arguments separate makes all reindexing and inclusion-exclusion steps
independent of determinant APIs.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`LaplaceExchange.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027]. This general algebra is intended for
Mathlib; its placement exception is recorded in `UPSTREAM.md`.
-/

public section

namespace Cslib

noncomputable section

open scoped BigOperators

namespace GenericMaximalMinor

section Permutations

variable {N : ℕ}

/-- Image of a finite subset under a permutation. -/
@[expose] def permImage (s : Equiv.Perm (Fin N)) (A : Finset (Fin N)) : Finset (Fin N) :=
  A.map s.toEmbedding

/-- Preimage of a finite subset under a permutation. -/
def permPreimage (s : Equiv.Perm (Fin N)) (A : Finset (Fin N)) : Finset (Fin N) :=
  A.map s.symm.toEmbedding

@[simp] lemma mem_permImage_iff (s : Equiv.Perm (Fin N))
    (A : Finset (Fin N)) (i : Fin N) :
    i ∈ permImage s A ↔ s.symm i ∈ A := by
  simp [permImage]

@[simp] lemma mem_permPreimage_iff (s : Equiv.Perm (Fin N))
    (A : Finset (Fin N)) (i : Fin N) :
    i ∈ permPreimage s A ↔ s i ∈ A := by
  simp [permPreimage]

@[simp] lemma permImage_permPreimage (s : Equiv.Perm (Fin N))
    (A : Finset (Fin N)) : permImage s (permPreimage s A) = A := by
  ext i
  simp

@[simp] lemma permPreimage_permImage (s : Equiv.Perm (Fin N))
    (A : Finset (Fin N)) : permPreimage s (permImage s A) = A := by
  ext i
  simp

lemma permImage_subset_iff (s : Equiv.Perm (Fin N))
    (A B : Finset (Fin N)) :
    permImage s A ⊆ B ↔ A ⊆ permPreimage s B := by
  constructor
  · intro h i hi
    simp only [mem_permPreimage_iff]
    apply h
    simp [hi]
  · intro h i hi
    simp only [mem_permImage_iff] at hi
    have := h hi
    simpa using this

lemma permPreimage_subset_iff (s : Equiv.Perm (Fin N))
    (A B : Finset (Fin N)) :
    permPreimage s A ⊆ B ↔ A ⊆ permImage s B := by
  constructor
  · intro h i hi
    simp only [mem_permImage_iff]
    apply h
    simpa using hi
  · intro h i hi
    simp only [mem_permPreimage_iff] at hi
    have himage := h hi
    simpa using himage

lemma permImage_eq_iff_eq_permPreimage (s : Equiv.Perm (Fin N))
    (A B : Finset (Fin N)) :
    permImage s A = B ↔ A = permPreimage s B := by
  constructor
  · intro h
    rw [← h, permPreimage_permImage]
  · rintro rfl
    exact permImage_permPreimage s B

end Permutations

section Exchange

variable {N R : Type*} [Fintype N] [DecidableEq N] [CommRing R]

/-- The determinant monomial in mathlib's row-permuting convention. -/
def determinantPermutationTerm (Y : Matrix N N R) (s : Equiv.Perm N) : R :=
  (Equiv.Perm.sign s : R) * ∏ i : N, Y (s i) i

end Exchange

section FinExchange

variable {N : ℕ} {R : Type*} [CommRing R]

/-- Permutation expansion of the signed Laplace product indexed by `A,B`. -/
@[expose] def laplacePermSum (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) : R :=
  ∑ s : Equiv.Perm (Fin N),
    if permImage s B = A then determinantPermutationTerm Y s else 0

/-- The matrix obtained by deleting the two off-diagonal blocks determined by
the row set `A` and column set `B`. -/
@[expose] def maskedMatrix (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) : Matrix (Fin N) (Fin N) R :=
  fun i j ↦ if (i ∈ A ↔ j ∈ B) then Y i j else 0

lemma permImage_eq_iff_forall_membership (s : Equiv.Perm (Fin N))
    (A B : Finset (Fin N)) :
    permImage s B = A ↔ ∀ i, (s i ∈ A ↔ i ∈ B) := by
  constructor
  · intro h i
    rw [← h]
    simp
  · intro h
    ext i
    simpa using (h (s.symm i)).symm

lemma determinantPermutationTerm_maskedMatrix
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (s : Equiv.Perm (Fin N)) :
    determinantPermutationTerm (maskedMatrix Y A B) s =
      if permImage s B = A then determinantPermutationTerm Y s else 0 := by
  classical
  by_cases h : permImage s B = A
  · have hall := (permImage_eq_iff_forall_membership s A B).mp h
    simp only [determinantPermutationTerm, maskedMatrix]
    simp_rw [ite_eq_left (hall _)]
    rw [ite_eq_left h]
  · have hex : ∃ i, ¬(s i ∈ A ↔ i ∈ B) := by
      by_contra hn
      push Not at hn
      exact h ((permImage_eq_iff_forall_membership s A B).mpr hn)
    rcases hex with ⟨i, hi⟩
    rw [ite_eq_right h]
    unfold determinantPermutationTerm
    have hfactor : maskedMatrix Y A B (s i) i = 0 := by
      simp [maskedMatrix, hi]
    have hprod : ∏ j : Fin N, maskedMatrix Y A B (s j) j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hfactor
    rw [hprod, mul_zero]

lemma laplacePermSum_eq_det_maskedMatrix
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) :
    laplacePermSum Y A B = Matrix.det (maskedMatrix Y A B) := by
  classical
  rw [laplacePermSum, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro s _
  exact (determinantPermutationTerm_maskedMatrix Y A B s).symm

/-- All subsets of `Fin N` containing `A`. -/
@[expose] def supersets (A : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  Finset.univ.powerset.filter fun U ↦ A ⊆ U

@[simp] lemma mem_supersets_iff (A U : Finset (Fin N)) :
    U ∈ supersets A ↔ A ⊆ U := by
  simp [supersets]

lemma sum_laplacePermSum_subsets (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) :
    (∑ V ∈ B.powerset, laplacePermSum Y A V) =
      ∑ s : Equiv.Perm (Fin N),
        if A ⊆ permImage s B then determinantPermutationTerm Y s else 0 := by
  classical
  simp_rw [laplacePermSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : A ⊆ permImage s B
  · have hmem : permPreimage s A ∈ B.powerset := by
      rw [Finset.mem_powerset, permPreimage_subset_iff]
      exact hs
    rw [ite_eq_left hs, Finset.sum_eq_single (permPreimage s A)]
    · simp
    · intro V hV hne
      rw [ite_eq_right]
      intro heq
      apply hne
      exact (permImage_eq_iff_eq_permPreimage s V A).mp heq
    · exact fun hnot ↦ (hnot hmem).elim
  · rw [ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro V hV
    rw [ite_eq_right]
    intro heq
    apply hs
    apply (permPreimage_subset_iff s A B).mp
    rw [← (permImage_eq_iff_eq_permPreimage s V A).mp heq]
    exact Finset.mem_powerset.mp hV

lemma sum_laplacePermSum_supersets (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) :
    (∑ U ∈ supersets A, laplacePermSum Y U B) =
      ∑ s : Equiv.Perm (Fin N),
        if A ⊆ permImage s B then determinantPermutationTerm Y s else 0 := by
  classical
  simp_rw [laplacePermSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : A ⊆ permImage s B
  · have hmem : permImage s B ∈ supersets A := by
      exact (mem_supersets_iff A (permImage s B)).mpr hs
    rw [ite_eq_left hs, Finset.sum_eq_single (permImage s B)]
    · simp
    · intro U hU hne
      rw [ite_eq_right]
      exact fun heq ↦ hne heq.symm
    · exact fun hnot ↦ (hnot hmem).elim
  · rw [ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro U hU
    rw [ite_eq_right]
    intro heq
    apply hs
    rw [heq]
    exact (mem_supersets_iff A U).mp hU

/-- Generalized Laplace exchange in permutation form. -/
theorem laplacePermSum_exchange (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) :
    (∑ V ∈ B.powerset, laplacePermSum Y A V) =
      ∑ U ∈ supersets A, laplacePermSum Y U B := by
  rw [sum_laplacePermSum_subsets, sum_laplacePermSum_supersets]

end FinExchange

end GenericMaximalMinor

end

end Cslib
