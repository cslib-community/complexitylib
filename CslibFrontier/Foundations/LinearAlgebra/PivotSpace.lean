/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Pivot spaces of a subspace of a product

For a subspace `V` of `Fin r → M`, the `i`-th *pivot space* consists of the `i`-th coordinates of
the vectors of `V` that vanish in all coordinates below `i`. This is the block-echelon form of `V`
used by Bourgain for affine extractors [Bourgain2007] and by Ben-Sasson and Kopparty
[BenSassonKopparty2012, Lemma 7.1]: choosing for each pivot vector a lift in `V` that vanishes
below its block presents `V` in block-triangular form, and the dimensions of the pivot spaces add
up to the dimension of `V`.

## Main definitions

* `Cslib.pivotSpace`: the `i`-th pivot space of a subspace of `Fin r → M`.

## Main results

* `Cslib.mem_pivotSpace`: pivot vectors lift to vectors of `V` vanishing below their block.
* `Cslib.sum_finrank_pivotSpace`: the dimensions of the pivot spaces add up to the dimension of `V`.

## References

* [J. Bourgain, *On the construction of affine extractors*][Bourgain2007]
* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib

open Module

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {r : ℕ}

/-- The `i`-th *pivot space* of `V ≤ Fin r → M`: the `i`-th coordinates of the vectors of `V`
that vanish in every coordinate below `i`. -/
def pivotSpace (V : Submodule K (Fin r → M)) (i : Fin r) : Submodule K M :=
  (V ⊓ ⨅ j : Fin r, ⨅ (_ : j < i), LinearMap.ker (LinearMap.proj j)).map (LinearMap.proj i)

/-- `y` lies in the `i`-th pivot space of `V` exactly when some `v ∈ V` vanishing in every
coordinate below `i` has `v i = y`. -/
theorem mem_pivotSpace {V : Submodule K (Fin r → M)} {i : Fin r} {y : M} :
    y ∈ pivotSpace V i ↔ ∃ v ∈ V, (∀ j < i, v j = 0) ∧ v i = y := by
  simp [pivotSpace, Submodule.mem_iInf, and_assoc]

/-- The vectors of `V` vanishing in the coordinates below `m`. -/
private def lowerZero (V : Submodule K (Fin r → M)) (m : ℕ) : Submodule K (Fin r → M) :=
  V ⊓ ⨅ j : Fin r, ⨅ (_ : (j : ℕ) < m), LinearMap.ker (LinearMap.proj j)

private theorem mem_lowerZero {V : Submodule K (Fin r → M)} {m : ℕ} {v : Fin r → M} :
    v ∈ lowerZero V m ↔ v ∈ V ∧ ∀ j : Fin r, (j : ℕ) < m → v j = 0 := by
  simp [lowerZero, Submodule.mem_iInf]

private theorem finrank_lowerZero [FiniteDimensional K M] (V : Submodule K (Fin r → M)) (m : ℕ)
    (hm : m < r) :
    finrank K (lowerZero V m) =
      finrank K (pivotSpace V ⟨m, hm⟩) + finrank K (lowerZero V (m + 1)) := by
  let f : lowerZero V m →ₗ[K] M := (LinearMap.proj ⟨m, hm⟩).comp (lowerZero V m).subtype
  have hrange : LinearMap.range f = pivotSpace V ⟨m, hm⟩ := by
    ext y
    simp only [LinearMap.mem_range, mem_pivotSpace, f, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, LinearMap.coe_proj, Function.eval]
    constructor
    · rintro ⟨⟨v, hv⟩, rfl⟩
      exact ⟨v, (mem_lowerZero.1 hv).1, fun j hj => (mem_lowerZero.1 hv).2 j hj, rfl⟩
    · rintro ⟨v, hv, hlow, rfl⟩
      exact ⟨⟨v, mem_lowerZero.2 ⟨hv, fun j hj => hlow j hj⟩⟩, rfl⟩
  have hle : lowerZero V (m + 1) ≤ lowerZero V m := fun v hv =>
    mem_lowerZero.2 ⟨(mem_lowerZero.1 hv).1, fun j hj => (mem_lowerZero.1 hv).2 j (by omega)⟩
  have hker : LinearMap.ker f = (lowerZero V (m + 1)).comap (lowerZero V m).subtype := by
    ext ⟨v, hv⟩
    simp only [LinearMap.mem_ker, f, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, LinearMap.coe_proj, Function.eval, Submodule.mem_comap,
      mem_lowerZero]
    constructor
    · intro h0
      refine ⟨(mem_lowerZero.1 hv).1, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact (mem_lowerZero.1 hv).2 j hj
      · rw [show j = ⟨m, hm⟩ from Fin.ext hj]
        exact h0
    · rintro ⟨-, h⟩
      exact h ⟨m, hm⟩ (Nat.lt_succ_self m)
  have := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at this
  exact this.symm

/-- The dimensions of the pivot spaces of `V` add up to the dimension of `V`. -/
theorem sum_finrank_pivotSpace [FiniteDimensional K M] (V : Submodule K (Fin r → M)) :
    ∑ i, finrank K (pivotSpace V i) = finrank K V := by
  classical
  have key : ∀ m ≤ r, finrank K (lowerZero V m) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin r => m ≤ (i : ℕ)), finrank K (pivotSpace V i) := by
    intro m hm
    induction hrm : r - m generalizing m with
    | zero =>
      have hmr : m = r := by omega
      subst hmr
      have hbot : lowerZero V m = ⊥ := by
        refine (Submodule.eq_bot_iff _).2 fun v hv => funext fun j => ?_
        exact (mem_lowerZero.1 hv).2 j j.2
      rw [hbot, finrank_bot, eq_comm]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact absurd i.2 (not_lt.2 (Finset.mem_filter.1 hi).2)
    | succ q ih =>
      have hmr : m < r := by omega
      rw [finrank_lowerZero V m hmr, ih (m + 1) (by omega) (by omega)]
      have hsplit : Finset.univ.filter (fun i : Fin r => m ≤ (i : ℕ)) =
          insert ⟨m, hmr⟩ (Finset.univ.filter fun i : Fin r => m + 1 ≤ (i : ℕ)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hsplit, Finset.sum_insert (by simp)]
  have h0 := key 0 (Nat.zero_le r)
  have hV : lowerZero V 0 = V := by
    ext v
    simp [mem_lowerZero]
  rw [hV] at h0
  rw [h0]
  exact Finset.sum_congr (by simp) fun _ _ => rfl

end Cslib
