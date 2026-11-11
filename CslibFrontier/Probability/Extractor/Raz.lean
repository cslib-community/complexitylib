/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey
public import CslibFrontier.Probability.Extractor.TwoSource
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Raz's Extractor

Raz's two-source extractor for one source with min-entropy > n/2 and a second source with
logarithmic min-entropy.

## Main definitions

* `Cslib.Probability.razExtractor`: The Raz extractor function.
* `Cslib.Probability.IsRazMatrixFamily`: The rank condition on the matrix family.

## Main theorem statement

* `Cslib.Probability.RazExtractorTheorem`: The correctness statement of Raz's extractor,
  formulated as a `Prop` to avoid `sorry` while the proof is being developed.
-/

public section

namespace Cslib.Probability

open Finset Cslib.Probability.PMF Matrix

variable {ι Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq ι]

/-- The condition on the matrix family for Raz's extractor: any non-trivial XOR sum
of up to `2 * t` matrices has rank at least `(1 - δ) * n`. -/
def IsRazMatrixFamily (M : Y → Matrix ι ι (ZMod 2)) (t : ℕ) (δ : ℝ) : Prop :=
  ∀ s : Finset Y, 0 < s.card → s.card ≤ 2 * t →
    (1 - δ) * Fintype.card ι ≤ (∑ y ∈ s, M y).rank

/-- The Raz extractor function. -/
def razExtractor (M : Y → Matrix ι ι (ZMod 2)) (x : (ι → ZMod 2) × (ι → ZMod 2))
    (y : Y) : ZMod 2 :=
  x.1 ⬝ᵥ (M y *ᵥ x.2)

/-- The statement that Raz's extractor is a two-source extractor.
Defined as a `Prop` to avoid `sorry` before the proof is complete. -/
def RazExtractorTheorem (M : Y → Matrix ι ι (ZMod 2)) (t : ℕ) (δ : ℝ) (C : ℝ) (ε : ℝ)
    (_hM : IsRazMatrixFamily M t δ) (k₁ k₂ : ℝ)
    (_hk₁ : (1 / 2 + δ) * Fintype.card ι ≤ k₁)
    (_hk₂ : C * Real.log (Fintype.card ι) ≤ k₂) : Prop :=
  IsTwoSourceExtractor (fun x y => (razExtractor M x y) = 1) k₁ k₂ ε

omit [Fintype Y] [DecidableEq ι] in
theorem razExtractor_add_left (M : Y → Matrix ι ι (ZMod 2)) (x₁ x₁' x₂ : ι → ZMod 2) (y : Y) :
    razExtractor M (x₁ + x₁', x₂) y = razExtractor M (x₁, x₂) y + razExtractor M (x₁', x₂) y := by
  simp [razExtractor, ]

omit [Fintype Y] [DecidableEq ι] in
theorem razExtractor_add_right (M : Y → Matrix ι ι (ZMod 2)) (x₁ x₂ x₂' : ι → ZMod 2) (y : Y) :
    razExtractor M (x₁, x₂ + x₂') y = razExtractor M (x₁, x₂) y + razExtractor M (x₁, x₂') y := by
  simp [razExtractor, mulVec_add]

omit [Fintype Y] [DecidableEq ι] in
theorem razExtractor_zero_left (M : Y → Matrix ι ι (ZMod 2)) (x₂ : ι → ZMod 2) (y : Y) :
    razExtractor M (0, x₂) y = 0 := by
  simp [razExtractor, zero_dotProduct]

omit [Fintype Y] [DecidableEq ι] in
theorem razExtractor_zero_right (M : Y → Matrix ι ι (ZMod 2)) (x₁ : ι → ZMod 2) (y : Y) :
    razExtractor M (x₁, 0) y = 0 := by
  simp [razExtractor, mulVec_zero, dotProduct_zero]

omit [Fintype Y] [DecidableEq ι] in
theorem ZMod.neg_one_pow_val_add {R : Type*} [Ring R] (a b : ZMod 2) :
    (-1 : R) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

omit [Fintype Y] [DecidableEq ι] in
theorem ZMod.neg_one_pow_val_sum {R : Type*} [CommRing R] {I : Type*} (s : Finset I)
    (f : I → ZMod 2) :
    (-1 : R) ^ (∑ i ∈ s, f i).val = ∏ i ∈ s, (-1) ^ (f i).val := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [sum_cons, prod_cons, ZMod.neg_one_pow_val_add, ih]

omit [Fintype Y] [DecidableEq ι] in
theorem sum_razExtractor (M : Y → Matrix ι ι (ZMod 2)) (x : (ι → ZMod 2) × (ι → ZMod 2))
    {I : Type*} (s : Finset I) (y : I → Y) :
    ∑ i ∈ s, razExtractor M x (y i) = x.1 ⬝ᵥ ((∑ i ∈ s, M (y i)) *ᵥ x.2) := by
  induction s using Finset.cons_induction with
  | empty => simp [razExtractor]
  | cons a s ha ih =>
    rw [sum_cons, sum_cons, add_mulVec, dotProduct_add, ← ih]
    rfl

omit [DecidableEq ι] in
theorem razExtractor_sum_pow_bias (q : Y → ℝ)
    (M : Y → Matrix ι ι (ZMod 2)) (x : (ι → ZMod 2) × (ι → ZMod 2)) (t : ℕ) :
    (∑ y, q y * (-1 : ℝ) ^ (razExtractor M x y).val) ^ (2 * t) =
      ∑ y : Fin (2 * t) → Y, (∏ i, q (y i)) * (-1 : ℝ) ^ (∑ i, razExtractor M x (y i)).val := by
  have := Fintype.sum_pow (fun y => q y * (-1 : ℝ) ^ (razExtractor M x y).val) (2 * t)
  rw [this]
  refine sum_congr rfl fun y _ => ?_
  rw [prod_mul_distrib]
  congr 1
  rw [← ZMod.neg_one_pow_val_sum]

omit [Fintype Y] [DecidableEq ι] in
theorem pow_sum_mul_le {I : Type*} [Fintype I] (P S : I → ℝ) (hP_nonneg : ∀ x, 0 ≤ P x)
    (hP_sum : ∑ x, P x = 1) (t : ℕ) :
    (∑ x, P x * S x) ^ (2 * t) ≤ ∑ x, P x * S x ^ (2 * t) := by
  have heven : Even (2 * t) := even_two_mul t
  have h_conv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 * t)) := Even.convexOn_pow heven
  have h_jensen := ConvexOn.map_sum_le h_conv (fun i _ => hP_nonneg i) hP_sum
    (fun i _ => Set.mem_univ (S i))
  simp_rw [smul_eq_mul] at h_jensen
  exact h_jensen

omit [Fintype Y] in
theorem sum_x1_x2_eq_two_pow_corank (M : Matrix ι ι (ZMod 2)) :
    ∑ x : (ι → ZMod 2) × (ι → ZMod 2), (-1 : ℝ) ^ (x.1 ⬝ᵥ (M *ᵥ x.2)).val =
    (2 : ℝ) ^ (2 * Fintype.card ι) / (2 : ℝ) ^ M.rank := by
  have h1 : ∑ x : (ι → ZMod 2) × (ι → ZMod 2), (-1 : ℝ) ^ (x.1 ⬝ᵥ (M *ᵥ x.2)).val =
      ∑ x1 : ι → ZMod 2, ∑ x2 : ι → ZMod 2, (-1 : ℝ) ^ (x1 ⬝ᵥ (M *ᵥ x2)).val := by
    rw [Fintype.sum_prod_type]
  have h1' : ∑ x1 : ι → ZMod 2, ∑ x2 : ι → ZMod 2, (-1 : ℝ) ^ (x1 ⬝ᵥ (M *ᵥ x2)).val =
      ∑ x2 : ι → ZMod 2, ∑ x1 : ι → ZMod 2, (-1 : ℝ) ^ (x1 ⬝ᵥ (M *ᵥ x2)).val := by
    rw [sum_comm]
  rw [h1, h1']
  have h2 : ∀ x2, ∑ x1 : ι → ZMod 2, (-1 : ℝ) ^ (x1 ⬝ᵥ (M *ᵥ x2)).val =
      if M *ᵥ x2 = 0 then (2 : ℝ) ^ Fintype.card ι else 0 := by
    intro x2
    exact sum_neg_one_pow_val_dotProduct (M *ᵥ x2)
  simp_rw [h2]
  have h3 : ∑ x2 : ι → ZMod 2, (if M *ᵥ x2 = 0 then (2 : ℝ) ^ Fintype.card ι else 0) =
      (#{z : ι → ZMod 2 | M *ᵥ z = 0} : ℝ) * (2 : ℝ) ^ Fintype.card ι := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  rw [h3]
  have h4 : (#{z : ι → ZMod 2 | M *ᵥ z = 0} : ℝ) * 2 ^ M.rank = (2 : ℝ) ^ Fintype.card ι := by
    exact_mod_cast card_ker_mul_two_pow_rank M
  have h5 : (#{z : ι → ZMod 2 | M *ᵥ z = 0} : ℝ) = (2 : ℝ) ^ Fintype.card ι / 2 ^ M.rank := by
    calc (#{z : ι → ZMod 2 | M *ᵥ z = 0} : ℝ) =
        (#{z : ι → ZMod 2 | M *ᵥ z = 0} : ℝ) * 2 ^ M.rank / 2 ^ M.rank := by
          rw [mul_div_cancel_right₀]
          positivity
      _ = (2 : ℝ) ^ Fintype.card ι / 2 ^ M.rank := by rw [h4]
  rw [h5, mul_comm, mul_div, ← pow_add, ← two_mul]

end Cslib.Probability
