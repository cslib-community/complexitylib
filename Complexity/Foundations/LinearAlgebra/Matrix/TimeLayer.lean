/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Matrix.CorrectionHierarchy
import Mathlib.Data.Fintype.Prod

/-!
# Time layers and terminal rewards

`Matrix.timeLayer T P` places a copy of `P` between each pair of consecutive clock layers
`0, …, T`. All other entries vanish, including the final rows. The lexicographic order makes
this matrix strictly upper triangular, even when `P` itself has cycles or absorbing states.
The reward `e` is paid only at time `T`. Its potential at `(i,x)` is exactly
`(P ^ (T - i) *ᵥ e) x`, which solves the actual clocked linear system. Nonnegative
substochastic `P` and rewards in `[0,1]` give a potential in `[0,1]` at every clocked state.

This is the matrix construction in [OpenAI2026LogSpace, Lemma 2.1], using the terminal-reward
convention of its proof. It does not enumerate configurations or assert a resource bound for
accessing the matrix. The machine and local-count specialization is in
`Classes.LogSpace.Randomized.TimeLayer`.

## Main definitions

* `Matrix.timeLayer`: transitions only to the next clock layer.
* `Matrix.timeLayerReward`: a reward supported on the last layer.
* `Matrix.timeLayerPotential`: the actual remaining-time matrix power.

## Main results

* `Matrix.timeLayer_isStrictUpperTriangular`, `Matrix.timeLayer_mulVec_one_le`:
  forwardness and the inherited row bound.
* `Matrix.one_sub_timeLayer_mulVec`: the potential solves the clocked system.
* `Matrix.inv_one_sub_timeLayer_mulVec`: its inverse-matrix expression.
* `Matrix.timeLayerPotential_mem_Icc`: the potential is bounded at every clocked state.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 2, Lemma 2.1, `model.tex`, terminal-time construction
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Matrix

open Finset

variable {V R : Type*}

/-- Place `P` between consecutive clock layers, with no outgoing edge from the last layer. -/
@[expose] def timeLayer [Zero R] (T : ℕ) (P : Matrix V V R) :
    Matrix (Lex (Fin (T + 1) × V)) (Lex (Fin (T + 1) × V)) R :=
  fun a b => if (ofLex a).1.val + 1 = (ofLex b).1.val then P (ofLex a).2 (ofLex b).2 else 0

/-- Pay the original reward only at the final clock layer. -/
@[expose] def timeLayerReward [Zero R] (T : ℕ) (e : V → R) : Lex (Fin (T + 1) × V) → R :=
  fun a => if (ofLex a).1.val = T then e (ofLex a).2 else 0

/-- The value at a clocked state after its actual remaining number of transitions. -/
@[expose] def timeLayerPotential [Fintype V] [DecidableEq V] [Semiring R]
    (T : ℕ) (P : Matrix V V R) (e : V → R) : Lex (Fin (T + 1) × V) → R :=
  fun a => (P ^ (T - (ofLex a).1.val) *ᵥ e) (ofLex a).2

/-- Clocking multiplies the number of states by exactly `T + 1`. -/
theorem card_timeLayer [Fintype V] (T : ℕ) :
    Fintype.card (Lex (Fin (T + 1) × V)) = (T + 1) * Fintype.card V := by
  rw [Fintype.card_congr (ofLex : Lex (Fin (T + 1) × V) ≃ Fin (T + 1) × V)]
  simp only [Fintype.card_prod, Fintype.card_fin]

/-- The clock alone supplies strict forwardness; no acyclicity of `P` is needed. -/
theorem timeLayer_isStrictUpperTriangular [LT V] [Zero R] (T : ℕ) (P : Matrix V V R) :
    (timeLayer T P).IsStrictUpperTriangular := by
  intro a b hab
  apply ite_eq_right
  intro hclock
  exact hab (Prod.Lex.lt_iff.mpr (Or.inl (show (ofLex a).1 < (ofLex b).1 by
    change (ofLex a).1.val < (ofLex b).1.val
    omega)))

/-- Every terminal row is zero, including when the horizon is zero. -/
theorem timeLayer_last [Zero R] (T : ℕ) (P : Matrix V V R) (x : V)
    (b : Lex (Fin (T + 1) × V)) : timeLayer T P (toLex (Fin.last T, x)) b = 0 := by
  apply ite_eq_right
  have hb := (ofLex b).1.isLt
  change ¬ T + 1 = (ofLex b).1.val
  omega

/-- A clocked row applies `P` to the next slice; at the horizon it vanishes. -/
theorem timeLayer_mulVec [Fintype V] [Semiring R] (T : ℕ) (P : Matrix V V R)
    (v : Lex (Fin (T + 1) × V) → R) (i : Fin (T + 1)) (x : V) :
    (timeLayer T P *ᵥ v) (toLex (i, x)) =
      if h : i.val < T then
        (P *ᵥ fun y => v (toLex (⟨i.val + 1, Nat.succ_lt_succ h⟩, y))) x else 0 := by
  classical
  unfold mulVec dotProduct
  rw [← (toLex : Fin (T + 1) × V ≃ Lex (Fin (T + 1) × V)).sum_comp]
  rw [Fintype.sum_prod_type]
  by_cases hi : i.val < T
  · rw [dite_eq_left hi]
    rw [sum_eq_single (⟨i.val + 1, Nat.succ_lt_succ hi⟩ : Fin (T + 1))]
    · simp [timeLayer]
    · intro j _ hj
      have hne : i.val + 1 ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp [timeLayer, hne]
    · simp
  · rw [dite_eq_right hi]
    refine sum_eq_zero fun j _ => ?_
    have hne : i.val + 1 ≠ j.val := by omega
    simp [timeLayer, hne]

/-- Nonnegative entries remain nonnegative after clocking. -/
theorem timeLayer_nonneg [Zero R] [Preorder R] {P : Matrix V V R}
    (hP : ∀ x y, 0 ≤ P x y) (T : ℕ) : ∀ a b, 0 ≤ timeLayer T P a b := by
  intro a b
  unfold timeLayer
  split_ifs
  · exact hP _ _
  · exact le_rfl

/-- Clocking preserves the substochastic row bound, with zero terminal rows. -/
theorem timeLayer_mulVec_one_le [Fintype V] [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {P : Matrix V V R} (hP : P *ᵥ 1 ≤ 1) (T : ℕ) : timeLayer T P *ᵥ 1 ≤ 1 := by
  intro a
  let i := (ofLex a).1
  let x := (ofLex a).2
  change (timeLayer T P *ᵥ 1) (toLex (i, x)) ≤ (1 : R)
  rw [timeLayer_mulVec]
  split_ifs
  · exact hP x
  · exact zero_le_one

/-- A substochastic matrix preserves `[0,1]` under every finite power. -/
theorem pow_mulVec_mem_Icc [Fintype V] [DecidableEq V]
    [Semiring R] [PartialOrder R] [IsOrderedRing R] {P : Matrix V V R} {e : V → R}
    (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : P *ᵥ 1 ≤ 1) (he : e ∈ Set.Icc 0 1) (t : ℕ) :
    P ^ t *ᵥ e ∈ Set.Icc 0 1 := by
  induction t with
  | zero => simpa using he
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec]
    exact ⟨mulVec_nonneg hP0 ih.1, mulVec_le_one hP0 hP1 ih.2⟩

/-- The actual remaining-time potential lies in `[0,1]` at every clocked state. -/
theorem timeLayerPotential_mem_Icc [Fintype V] [DecidableEq V]
    [Semiring R] [PartialOrder R] [IsOrderedRing R] {P : Matrix V V R} {e : V → R}
    (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : P *ᵥ 1 ≤ 1) (he : e ∈ Set.Icc 0 1) (T : ℕ) :
    timeLayerPotential T P e ∈ Set.Icc 0 1 := by
  constructor <;> intro a
  · exact (pow_mulVec_mem_Icc hP0 hP1 he _).1 _
  · exact (pow_mulVec_mem_Icc hP0 hP1 he _).2 _

/-- At clock zero, the potential is the original `T`-step terminal expectation. -/
theorem timeLayerPotential_zero [Fintype V] [DecidableEq V] [Semiring R]
    (T : ℕ) (P : Matrix V V R) (e : V → R) (x : V) :
    timeLayerPotential T P e (toLex (0, x)) = (P ^ T *ᵥ e) x := by
  simp [timeLayerPotential]

/-- The clocked potential solves the actual linear system, with reward only at final time. -/
theorem one_sub_timeLayer_mulVec [Fintype V] [DecidableEq V] [Ring R]
    (T : ℕ) (P : Matrix V V R) (e : V → R) :
    (1 - timeLayer T P) *ᵥ timeLayerPotential T P e = timeLayerReward T e := by
  rw [sub_mulVec, one_mulVec]
  ext a
  let i := (ofLex a).1
  let x := (ofLex a).2
  change timeLayerPotential T P e (toLex (i, x)) -
    (timeLayer T P *ᵥ timeLayerPotential T P e) (toLex (i, x)) =
      timeLayerReward T e (toLex (i, x))
  rw [timeLayer_mulVec]
  by_cases hi : i.val < T
  · rw [dite_eq_left hi]
    have hne : i.val ≠ T := by omega
    have hremaining : T - i.val = T - (i.val + 1) + 1 := by omega
    change (P ^ (T - i.val) *ᵥ e) x -
      (P *ᵥ (P ^ (T - (i.val + 1)) *ᵥ e)) x = if i.val = T then e x else 0
    rw [ite_eq_right hne, mulVec_mulVec, ← pow_succ', ← hremaining, sub_self]
  · rw [dite_eq_right hi]
    have hiT : i.val = T := by omega
    simp [timeLayerPotential, timeLayerReward, hiT]

/-- The clocked linear system has determinant one over any commutative ring. -/
theorem det_one_sub_timeLayer [Fintype V] [LinearOrder V] [CommRing R]
    (T : ℕ) (P : Matrix V V R) : (1 - timeLayer T P).det = 1 := by
  rw [sub_eq_add_neg]
  exact (timeLayer_isStrictUpperTriangular T P).neg.det_one_add

/-- The inverse expression equals the explicitly constructed remaining-time potential. -/
theorem inv_one_sub_timeLayer_mulVec [Fintype V] [LinearOrder V] [CommRing R]
    (T : ℕ) (P : Matrix V V R) (e : V → R) :
    (1 - timeLayer T P)⁻¹ *ᵥ timeLayerReward T e = timeLayerPotential T P e := by
  have hu : IsUnit (1 - timeLayer T P).det := by rw [det_one_sub_timeLayer]; exact isUnit_one
  rw [← one_sub_timeLayer_mulVec T P e, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]

end Matrix
