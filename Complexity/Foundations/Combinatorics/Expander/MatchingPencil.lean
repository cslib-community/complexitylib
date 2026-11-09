/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Matrix.Hyperplane
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Matching-path spectral pencils

Eliminating the internal vertices of equal-length paths added along a matching gives the core
matrix `L + q (c P - M) - δ D`. Here `P` selects the matched core vertices, `M` is the matching
matrix, `D = 3 I - P`, and `L` is the core Laplacian. For a path of length `ℓ`, the parameters are
`q = sin θ / sin (ℓ θ)`, `c = cos (ℓ θ)`, and `δ = 1 - cos θ`.

This module proves the finite matrix certificate behind the construction. A core quadratic-form
gap greater than `2 q + 3 δ` makes the pencil positive on mean-zero vectors. Its value on the
constant vector is negative, so the pencil is nonsingular. The signless branch is positive on
the whole space and accommodates either parity of the added paths.

Weights in `[0,1]` are allowed: the ordinary matching case takes `w` to be the indicator of the
matched vertices and an involution `σ` pairing them. Fixed points of `σ` outside the support do
not matter. These are matrix certificates; this module does not construct a subdivided graph or
assert the existence of a near-Ramanujan core family.

## Main results

* `Cslib.MatchingPencil.abs_dotProduct_weightedMatching_le`: the matching quadratic-form bound.
* `Cslib.MatchingPencil.pencil_lower_bound`: the perturbation budget `2 q + 3 δ`.
* `Cslib.MatchingPencil.laplacianPencil_injective`: nonsingularity on the Laplacian branch.
* `Cslib.MatchingPencil.signlessPencil_injective`: nonsingularity on the signless branch.

The certificate and its use for matching-path expansion are derived here. The proof uses the
elementary hyperplane criterion rather than an eigenvalue perturbation theorem.
-/

@[expose] public section

namespace Cslib.MatchingPencil

open Matrix Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The adjacency matrix of a weighted matching, represented by an involutive permutation that
preserves the weights. The definition also makes sense before those hypotheses are imposed. -/
def weightedMatching (w : V → ℝ) (σ : Equiv.Perm V) : Matrix V V ℝ :=
  diagonal w * σ.permMatrix ℝ

/-- The core degree matrix when a matched vertex has degree two and an unmatched vertex has
degree three. Indicator weights give precisely those two cases. -/
def coreDegree (w : V → ℝ) : Matrix V V ℝ := diagonal (fun v => 3 - w v)

/-- The core pencil after path elimination; `s = -1` is the positive-eigenvalue branch, and
`s = (-1)^(ℓ+1)` is the negative-eigenvalue branch. -/
def pencil (B : Matrix V V ℝ) (w : V → ℝ) (σ : Equiv.Perm V)
    (q c s δ : ℝ) : Matrix V V ℝ :=
  B + q • (c • diagonal w + s • weightedMatching w σ) - δ • coreDegree w

/-- Multiplication by a weighted matching evaluates the vector at the matched vertex. -/
@[simp]
theorem weightedMatching_mulVec (w : V → ℝ) (σ : Equiv.Perm V) (x : V → ℝ) (v : V) :
    (weightedMatching w σ *ᵥ x) v = w v * x (σ v) := by
  rw [weightedMatching, ← mulVec_mulVec, permMatrix_mulVec, mulVec_diagonal]
  rfl

/-- An involution preserving the vertex weights gives a symmetric matching matrix. -/
theorem weightedMatching_isSymm (w : V → ℝ) (σ : Equiv.Perm V)
    (hσ : Function.Involutive σ) (hw : ∀ v, w (σ v) = w v) :
    (weightedMatching w σ).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [weightedMatching, diagonal_mul, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
  by_cases h : σ i = j
  · subst j
    simp [hσ i, hw]
  · have h' : σ j ≠ i := fun he => h (by rw [← he, hσ])
    simp [Ne.symm h, Ne.symm h']

/-- The matching sends the constant vector to the vector of vertex weights. -/
@[simp]
theorem weightedMatching_mulVec_one (w : V → ℝ) (σ : Equiv.Perm V) :
    weightedMatching w σ *ᵥ (1 : V → ℝ) = w := by
  ext v
  simp

/-- The matching quadratic form is bounded by the weighted squared norm. -/
theorem abs_dotProduct_weightedMatching_le (w : V → ℝ) (σ : Equiv.Perm V)
    (hw0 : ∀ v, 0 ≤ w v) (hwσ : ∀ v, w (σ v) = w v) (x : V → ℝ) :
    |x ⬝ᵥ weightedMatching w σ *ᵥ x| ≤ x ⬝ᵥ diagonal w *ᵥ x := by
  have hsum : ∑ v, w v * x (σ v) ^ 2 = ∑ v, w v * x v ^ 2 := by
    simpa only [hwσ] using Equiv.sum_comp σ (fun v => w v * x v ^ 2)
  have hbound (v : V) :
      |x v * (w v * x (σ v))| ≤ (w v * x v ^ 2 + w v * x (σ v) ^ 2) / 2 := by
    have h := sq_nonneg (|x v| - |x (σ v)|)
    have hw := mul_nonneg (hw0 v) h
    simp only [sub_sq, sq_abs] at hw
    rw [abs_mul, abs_mul, abs_of_nonneg (hw0 v)]
    nlinarith [hw]
  calc
    |x ⬝ᵥ weightedMatching w σ *ᵥ x|
        = |∑ v, x v * (w v * x (σ v))| := by simp only [dotProduct, weightedMatching_mulVec]
    _ ≤ ∑ v, |x v * (w v * x (σ v))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v, (w v * x v ^ 2 + w v * x (σ v) ^ 2) / 2 :=
      sum_le_sum fun v _ => hbound v
    _ = ∑ v, w v * x v ^ 2 := by rw [← sum_div, sum_add_distrib, hsum]; ring
    _ = x ⬝ᵥ diagonal w *ᵥ x := by
      simp only [dotProduct, mulVec_diagonal]
      apply sum_congr rfl
      intro v _
      ring

/-- The weighted norm lies between zero and the ordinary squared norm. -/
theorem diagonal_form_bounds (w : V → ℝ) (hw0 : ∀ v, 0 ≤ w v) (hw1 : ∀ v, w v ≤ 1)
    (x : V → ℝ) : 0 ≤ x ⬝ᵥ diagonal w *ᵥ x ∧ x ⬝ᵥ diagonal w *ᵥ x ≤ x ⬝ᵥ x := by
  simp only [dotProduct, mulVec_diagonal]
  constructor
  · exact sum_nonneg fun v _ => by nlinarith [mul_nonneg (hw0 v) (sq_nonneg (x v))]
  · apply sum_le_sum
    intro v _
    nlinarith [mul_nonneg (sub_nonneg.mpr (hw1 v)) (sq_nonneg (x v))]

/-- The degree quadratic form is `3 ‖x‖²` minus the weighted norm. -/
theorem coreDegree_form (w : V → ℝ) (x : V → ℝ) :
    x ⬝ᵥ coreDegree w *ᵥ x = 3 * (x ⬝ᵥ x) - x ⬝ᵥ diagonal w *ᵥ x := by
  simp only [coreDegree, dotProduct, mulVec_diagonal, mul_sub, sub_mul,
    sum_sub_distrib]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro v _
  ring

/-- Expanding the pencil quadratic form isolates its three scalar perturbation terms. -/
theorem pencil_form (B : Matrix V V ℝ) (w : V → ℝ) (σ : Equiv.Perm V)
    (q c s δ : ℝ) (x : V → ℝ) :
    x ⬝ᵥ pencil B w σ q c s δ *ᵥ x = x ⬝ᵥ B *ᵥ x +
      q * (c * (x ⬝ᵥ diagonal w *ᵥ x) + s * (x ⬝ᵥ weightedMatching w σ *ᵥ x)) -
        δ * (x ⬝ᵥ coreDegree w *ᵥ x) := by
  simp only [pencil, sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub,
    dotProduct_add, dotProduct_smul, smul_eq_mul]

/-- The matching perturbation costs at most `2 q + 3 δ` in the quadratic-form gap. -/
theorem pencil_lower_bound (B : Matrix V V ℝ) (w : V → ℝ) (σ : Equiv.Perm V)
    (hw0 : ∀ v, 0 ≤ w v) (hw1 : ∀ v, w v ≤ 1) (hwσ : ∀ v, w (σ v) = w v)
    {q c s δ : ℝ} (hq : 0 ≤ q) (hc : |c| ≤ 1) (hs : |s| ≤ 1) (hδ : 0 ≤ δ)
    (x : V → ℝ) :
    x ⬝ᵥ B *ᵥ x - (2 * q + 3 * δ) * (x ⬝ᵥ x) ≤
      x ⬝ᵥ pencil B w σ q c s δ *ᵥ x := by
  obtain ⟨hp0, hp1⟩ := diagonal_form_bounds w hw0 hw1 x
  have hm := (abs_dotProduct_weightedMatching_le w σ hw0 hwσ x).trans hp1
  have hcp : |c * (x ⬝ᵥ diagonal w *ᵥ x)| ≤ x ⬝ᵥ x := by
    rw [abs_mul, abs_of_nonneg hp0]
    simpa only [one_mul] using mul_le_mul hc hp1 hp0 zero_le_one
  have hsm : |s * (x ⬝ᵥ weightedMatching w σ *ᵥ x)| ≤ x ⬝ᵥ x := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hs hm (abs_nonneg _) zero_le_one
  have hpert := mul_le_mul_of_nonneg_left (add_le_add (neg_le_of_abs_le hcp)
    (neg_le_of_abs_le hsm)) hq
  have hdeg : x ⬝ᵥ coreDegree w *ᵥ x ≤ 3 * (x ⬝ᵥ x) := by
    rw [coreDegree_form]
    linarith
  have hd := mul_le_mul_of_nonneg_left hdeg hδ
  rw [pencil_form]
  nlinarith

/-- A symmetric core gives a symmetric matching pencil. -/
theorem pencil_isSymm {B : Matrix V V ℝ} (hB : B.IsSymm) (w : V → ℝ)
    (σ : Equiv.Perm V) (hσ : Function.Involutive σ) (hwσ : ∀ v, w (σ v) = w v)
    (q c s δ : ℝ) : (pencil B w σ q c s δ).IsSymm :=
  (hB.add (((isSymm_diagonal w).smul c).add
    ((weightedMatching_isSymm w σ hσ hwσ).smul s) |>.smul q)).sub
      ((isSymm_diagonal _).smul δ)

/-- The positive-eigenvalue pencil is nonsingular when the core Laplacian gap exceeds the
perturbation budget. The matching must have positive total weight. -/
theorem laplacianPencil_injective {L : Matrix V V ℝ} (hL : L.IsSymm)
    (hLone : L *ᵥ (1 : V → ℝ) = 0) (w : V → ℝ) (σ : Equiv.Perm V)
    (hσ : Function.Involutive σ) (hw0 : ∀ v, 0 ≤ w v) (hw1 : ∀ v, w v ≤ 1)
    (hwσ : ∀ v, w (σ v) = w v) (hwpos : 0 < ∑ v, w v)
    {μ q c δ : ℝ}
    (hgap : ∀ x : V → ℝ, (1 : V → ℝ) ⬝ᵥ x = 0 → μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ L *ᵥ x)
    (hq : 0 < q) (hc : |c| ≤ 1) (hc1 : c < 1) (hδ : 0 ≤ δ)
    (hbudget : 2 * q + 3 * δ < μ) :
    Function.Injective (pencil L w σ q c (-1) δ).mulVec := by
  apply Matrix.mulVec_injective_of_pos_on_orthogonal
    (pencil_isSymm hL w σ hσ hwσ q c (-1) δ) (e := 1)
  · intro x hx hx0
    have hnorm0 : 0 ≤ x ⬝ᵥ x := sum_nonneg fun v _ => mul_self_nonneg (x v)
    have hnorm : 0 < x ⬝ᵥ x := lt_of_le_of_ne hnorm0
      (Ne.symm (mt dotProduct_self_eq_zero.mp hx0))
    have hlo := pencil_lower_bound L w σ hw0 hw1 hwσ hq.le hc
      (by norm_num : |(-1 : ℝ)| ≤ 1) hδ x
    have := hgap x hx
    have := mul_pos (sub_pos.mpr hbudget) hnorm
    nlinarith
  · have hp : (1 : V → ℝ) ⬝ᵥ diagonal w *ᵥ (1 : V → ℝ) = ∑ v, w v := by
      simp [dotProduct, mulVec_diagonal]
    have hm : (1 : V → ℝ) ⬝ᵥ weightedMatching w σ *ᵥ (1 : V → ℝ) = ∑ v, w v := by
      simp [dotProduct]
    have hd : 0 ≤ (1 : V → ℝ) ⬝ᵥ coreDegree w *ᵥ (1 : V → ℝ) := by
      simp only [coreDegree, dotProduct, mulVec_diagonal, Pi.one_apply, mul_one, one_mul]
      exact sum_nonneg fun v _ => by linarith [hw1 v]
    rw [pencil_form, hLone, dotProduct_zero, hp, hm]
    have := mul_pos hq (mul_pos (sub_pos.mpr hc1) hwpos)
    have := mul_nonneg hδ hd
    nlinarith

/-- A signless core gap larger than the same budget makes either parity pencil nonsingular.
Unlike the Laplacian branch, positivity is assumed on the entire vector space. -/
theorem signlessPencil_injective (Q : Matrix V V ℝ) (w : V → ℝ) (σ : Equiv.Perm V)
    (hw0 : ∀ v, 0 ≤ w v) (hw1 : ∀ v, w v ≤ 1) (hwσ : ∀ v, w (σ v) = w v)
    {ν q c s δ : ℝ} (hgap : ∀ x : V → ℝ, ν * (x ⬝ᵥ x) ≤ x ⬝ᵥ Q *ᵥ x)
    (hq : 0 ≤ q) (hc : |c| ≤ 1) (hs : |s| ≤ 1) (hδ : 0 ≤ δ)
    (hbudget : 2 * q + 3 * δ < ν) :
    Function.Injective (pencil Q w σ q c s δ).mulVec := by
  intro x y hxy
  apply sub_eq_zero.mp
  by_contra hne
  let z := x - y
  have hz : pencil Q w σ q c s δ *ᵥ z = 0 := by
    change pencil Q w σ q c s δ *ᵥ (x - y) = 0
    rw [mulVec_sub, hxy, sub_self]
  have hnorm0 : 0 ≤ z ⬝ᵥ z := sum_nonneg fun v _ => mul_self_nonneg (z v)
  have hnorm : 0 < z ⬝ᵥ z := lt_of_le_of_ne hnorm0
    (Ne.symm (mt dotProduct_self_eq_zero.mp hne))
  have hlo := pencil_lower_bound Q w σ hw0 hw1 hwσ hq hc hs hδ z
  rw [hz, dotProduct_zero] at hlo
  have := hgap z
  have := mul_pos (sub_pos.mpr hbudget) hnorm
  nlinarith

end Cslib.MatchingPencil
