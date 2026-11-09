/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, generic maximal minors)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.MaximalMinor.SignedLaplaceProduct

/-!
# Inclusion--exclusion consequences of generalized Laplace exchange

This file isolates the finite-set Möbius inversion used by both branches of
Laplace straightening.  It is stated over an arbitrary commutative ring so the
same theorem can later be specialized to integer coefficients and to generic
polynomial rings.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`LaplaceInclusionExclusion.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027]. This general algebra is intended for
Mathlib; its destination is recorded in the upstream marker above.
-/

public section

namespace Cslib

noncomputable section

open scoped BigOperators

namespace GenericMaximalMinor

variable {α R : Type*} [DecidableEq α] [CommRing R]

lemma sum_powerset_neg_one_pow_card_cast (S : Finset α) :
    (∑ W ∈ S.powerset, (-1 : R) ^ W.card) = if S = ∅ then 1 else 0 := by
  have h := Finset.sum_powerset_neg_one_pow_card (x := S)
  have hcast := congrArg (Int.castRingHom R) h
  simpa using hcast

lemma sum_powerset_sdiff (B W : Finset α) (f : Finset α → R) :
    (∑ V ∈ (B \ W).powerset, f V) =
      ∑ V ∈ B.powerset, if Disjoint V W then f V else 0 := by
  classical
  have hfilter :
      (B \ W).powerset = B.powerset.filter fun V ↦ Disjoint V W := by
    ext V
    simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_sdiff]
  rw [hfilter, Finset.sum_filter]

/-- The two natural descriptions of the disjoint pairs `(W,V)` occurring in
finite-set inclusion--exclusion. -/
lemma sum_powerset_sdiff_swap (C B : Finset α) (f : Finset α → Finset α → R) :
    (∑ W ∈ C.powerset, ∑ V ∈ (B \ W).powerset, f W V) =
      ∑ V ∈ B.powerset, ∑ W ∈ (C \ V).powerset, f W V := by
  classical
  simp_rw [sum_powerset_sdiff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro V _
  apply Finset.sum_congr rfl
  intro W _
  by_cases h : Disjoint V W
  · simp [h, h.symm]
  · have h' : ¬Disjoint W V := fun hw ↦ h hw.symm
    simp [h, h']

/-- Finite-set Möbius filtering: alternating over the elements forbidden from
`V` retains precisely the terms with `C ⊆ V`. -/
theorem powerset_mobius_filter (C B : Finset α) (_hCB : C ⊆ B)
    (f : Finset α → R) :
    (∑ W ∈ C.powerset, (-1 : R) ^ W.card *
        ∑ V ∈ (B \ W).powerset, f V) =
      ∑ V ∈ B.powerset, if C ⊆ V then f V else 0 := by
  classical
  simp_rw [Finset.mul_sum]
  rw [sum_powerset_sdiff_swap C B (fun W V ↦ (-1 : R) ^ W.card * f V)]
  apply Finset.sum_congr rfl
  intro V hVB
  rw [← Finset.sum_mul]
  rw [sum_powerset_neg_one_pow_card_cast]
  by_cases hCV : C ⊆ V
  · have hempty : C \ V = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hCV
    rw [ite_eq_left hempty, ite_eq_left hCV, one_mul]
  · have hnonempty : C \ V ≠ ∅ := by
      exact fun h ↦ hCV (Finset.sdiff_eq_empty_iff_subset.mp h)
    rw [ite_eq_right hnonempty, ite_eq_right hCV, zero_mul]

section Laplace

variable {N : ℕ}

/-- Subsets lying in the interval `[C,B]` of the inclusion poset. -/
@[expose] def betweenSubsets (C B : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  B.powerset.filter fun V ↦ C ⊆ V

@[simp] lemma mem_betweenSubsets_iff (C B V : Finset (Fin N)) :
    V ∈ betweenSubsets C B ↔ C ⊆ V ∧ V ⊆ B := by
  simp [betweenSubsets, and_comm]

/-- Complement reindexes subsets of `B` as supersets of `Bᶜ`. -/
lemma sum_powerset_compl (B : Finset (Fin N))
    (f : Finset (Fin N) → R) :
    (∑ V ∈ B.powerset, f Vᶜ) = ∑ W ∈ supersets Bᶜ, f W := by
  classical
  refine Finset.sum_bij (fun V _ ↦ Vᶜ) ?_ ?_ ?_ ?_
  · intro V hV
    rw [mem_supersets_iff]
    exact Finset.compl_subset_compl.mpr (Finset.mem_powerset.mp hV)
  · intro V hV W hW heq
    simpa using congrArg (fun S : Finset (Fin N) ↦ Sᶜ) heq
  · intro W hW
    have hsub : Wᶜ ⊆ B := by
      have := Finset.compl_subset_compl.mpr (mem_supersets_iff Bᶜ W |>.mp hW)
      simpa using this
    exact ⟨Wᶜ, Finset.mem_powerset.mpr hsub, by simp⟩
  · intro V hV
    rfl

/-- First inclusion--exclusion form of generalized Laplace exchange. -/
theorem laplacePermSum_exchange_inclusionExclusion_one
    (Y : Matrix (Fin N) (Fin N) R)
    (A B C : Finset (Fin N)) (hCB : C ⊆ B) :
    (∑ V ∈ betweenSubsets C B, laplacePermSum Y A V) =
      ∑ U ∈ supersets A, ∑ W ∈ C.powerset,
        (-1 : R) ^ W.card * laplacePermSum Y U (B \ W) := by
  classical
  symm
  calc
    (∑ U ∈ supersets A, ∑ W ∈ C.powerset,
        (-1 : R) ^ W.card * laplacePermSum Y U (B \ W)) =
        ∑ W ∈ C.powerset, (-1 : R) ^ W.card *
          ∑ U ∈ supersets A, laplacePermSum Y U (B \ W) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = ∑ W ∈ C.powerset, (-1 : R) ^ W.card *
          ∑ V ∈ (B \ W).powerset, laplacePermSum Y A V := by
      apply Finset.sum_congr rfl
      intro W _
      congr 1
      exact (laplacePermSum_exchange Y A (B \ W)).symm
    _ = ∑ V ∈ B.powerset,
          if C ⊆ V then laplacePermSum Y A V else 0 :=
      powerset_mobius_filter C B hCB (laplacePermSum Y A)
    _ = ∑ V ∈ betweenSubsets C B, laplacePermSum Y A V := by
      rw [betweenSubsets, Finset.sum_filter]

/-- Second, complement-symmetric inclusion--exclusion form. -/
theorem laplacePermSum_exchange_inclusionExclusion_two
    (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) :
    (∑ U ∈ supersets A, ∑ W ∈ supersets B,
        (-1 : R) ^ Wᶜ.card * laplacePermSum Y U W) =
      ∑ V ∈ B.powerset, laplacePermSum Y A Vᶜ := by
  classical
  have hie := laplacePermSum_exchange_inclusionExclusion_one
    (Y := Y) A (Finset.univ : Finset (Fin N)) Bᶜ (Finset.subset_univ _)
  have hbetween :
      betweenSubsets Bᶜ (Finset.univ : Finset (Fin N)) = supersets Bᶜ := by
    ext V
    simp [betweenSubsets]
  have hleft :
      (∑ V ∈ betweenSubsets Bᶜ (Finset.univ : Finset (Fin N)),
          laplacePermSum Y A V) =
        ∑ V ∈ B.powerset, laplacePermSum Y A Vᶜ := by
    rw [hbetween]
    exact (sum_powerset_compl B (laplacePermSum Y A)).symm
  have hinner (U : Finset (Fin N)) :
      (∑ W ∈ Bᶜ.powerset, (-1 : R) ^ W.card *
          laplacePermSum Y U ((Finset.univ : Finset (Fin N)) \ W)) =
        ∑ W ∈ supersets B, (-1 : R) ^ Wᶜ.card * laplacePermSum Y U W := by
    simpa only [← Finset.compl_eq_univ_sdiff, compl_compl] using
      sum_powerset_compl (R := R) Bᶜ
      (fun W ↦ (-1 : R) ^ Wᶜ.card * laplacePermSum Y U W)
  have hright :
      (∑ U ∈ supersets A, ∑ W ∈ Bᶜ.powerset,
          (-1 : R) ^ W.card *
            laplacePermSum Y U ((Finset.univ : Finset (Fin N)) \ W)) =
        ∑ U ∈ supersets A, ∑ W ∈ supersets B,
          (-1 : R) ^ Wᶜ.card * laplacePermSum Y U W := by
    apply Finset.sum_congr rfl
    intro U _
    exact hinner U
  exact hright.symm.trans (hie.symm.trans hleft)

end Laplace

end GenericMaximalMinor

end

end Cslib
