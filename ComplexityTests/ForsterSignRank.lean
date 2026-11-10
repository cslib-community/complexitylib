/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Communication.Forster
import Complexity.Computability.Communication.InnerProductRank
import Complexity.Foundations.LinearAlgebra.Matrix.IsotropicPosition

/-!
Regression clients for Forster's sign-rank bound: approximate isotropic weights for a concrete
configuration in general position, the bilinear and spectral-norm forms of the bound, and the
resulting sign-rank and unbounded-error lower bounds for the inner product on small inputs.
-/

open Cslib Cslib.Communication Finset Matrix

namespace ForsterTests

/-! ### Approximate isotropic position -/

/-- Two nonzero vectors in `ℝ¹` are in general position. -/
theorem genPos_two : ∀ e : Fin 1 ↪ Fin 2,
    ((Matrix.of fun (x : Fin 2) (_ : Fin 1) => ((x : ℕ) + 1 : ℝ)).submatrix e id).det ≠ 0 := by
  intro e
  rw [det_fin_one]
  simp only [submatrix_apply, of_apply, id]
  positivity

-- Hence they can be weighted so that each leverage is at most `1 / 2 + ε`.
example {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Fin 2 → ℝ, (∀ x, 0 < p x) ∧
      ∀ x, p x * ((Matrix.of fun (x : Fin 2) (_ : Fin 1) => ((x : ℕ) + 1 : ℝ)) x ⬝ᵥ
        ((∑ z, p z • vecMulVec ((Matrix.of fun (x : Fin 2) (_ : Fin 1) => ((x : ℕ) + 1 : ℝ)) z)
          ((Matrix.of fun (x : Fin 2) (_ : Fin 1) => ((x : ℕ) + 1 : ℝ)) z))⁻¹ *ᵥ
          (Matrix.of fun (x : Fin 2) (_ : Fin 1) => ((x : ℕ) + 1 : ℝ)) x)) ≤ 1 / 2 + ε := by
  obtain ⟨p, hp, -, hlev⟩ := exists_isotropic_weights _ genPos_two (by simp) hε
  exact ⟨p, hp, fun x => by simpa using hlev x⟩

-- Any configuration is moved into general position by a small generic perturbation.
example (U : Matrix (Fin 3) (Fin 2) ℝ) : ∃ W : Matrix (Fin 3) (Fin 2) ℝ, ∃ ε : ℝ,
    ∀ e : Fin 2 ↪ Fin 3, ((U + ε • W).submatrix e id).det ≠ 0 := by
  obtain ⟨W, hW⟩ := eventually_det_submatrix_add_smul_ne_zero U
  obtain ⟨ε, hε⟩ := hW.exists
  exact ⟨W, ε, hε⟩

/-! ### Forster's bound -/

-- The bilinear form, with margin `2` for `2 •` a sign matrix.
example (f : Fin 3 → Fin 2 → Bool) {lam : ℝ}
    (hspec : ∀ (p : Fin 3 → ℝ) (q : Fin 2 → ℝ),
      |∑ x, ∑ y, p x * (2 • signMatrix ℝ f) x y * q y| ≤
        lam * √(∑ x, p x ^ 2) * √(∑ y, q y ^ 2)) :
    2 * √(3 * 2) ≤ lam * signRank f := by
  have := mul_sqrt_card_mul_card_le_mul_signRank f (2 • signMatrix ℝ f) (μ := 2)
    (fun x y => by
      simp only [Matrix.smul_apply, signMatrix_apply, nsmul_eq_mul]
      split_ifs <;> norm_num) hspec
  simpa using this

open scoped Matrix.Norms.L2Operator in
-- The spectral-norm form for a general matrix and for a sign matrix.
example (f : Fin 2 → Fin 2 → Bool) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : ∀ x y, 1 ≤ signMatrix ℝ f x y * M x y) :
    √(2 * 2) ≤ ‖M‖ * signRank f := by
  simpa using mul_sqrt_card_mul_card_le_l2_opNorm_mul_signRank f M hM

open scoped Matrix.Norms.L2Operator in
example (f : Fin 4 → Fin 4 → Bool) : √(4 * 4) ≤ ‖signMatrix ℝ f‖ * signRank f := by
  simpa using sqrt_card_mul_card_le_l2_opNorm_mul_signRank f

/-! ### Hadamard matrices and the inner product -/

-- The `4 × 4` Sylvester–Hadamard sign matrix (inner product on two bits) has sign-rank at
-- least `2`, through the general Hadamard bound.
example : 4 ≤ signRank (fun x y : Fin 2 → Bool => x ⬝ᵥ y) ^ 2 := by
  simpa using card_le_signRank_sq_of_isHadamard (isHadamard_signMatrix_dotProduct ℝ (ι := Fin 2))


-- The inner product on three bits has sign-rank at least `3` (`8 ≤ d²`).
example : 3 ≤ signRank (fun x y : Fin 3 → Bool => x ⬝ᵥ y) := by
  have h := two_pow_card_le_signRank_dotProduct_sq (ι := Fin 3)
  simp only [Fintype.card_fin] at h
  by_contra hlt
  push Not at hlt
  have : signRank (fun x y : Fin 3 → Bool => x ⬝ᵥ y) ^ 2 ≤ 2 ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  omega

-- The inner product on four bits has sign-rank at least `4`.
example : 4 ≤ signRank (fun x y : Fin 4 → Bool => x ⬝ᵥ y) := by
  have h := two_pow_card_le_signRank_dotProduct_sq (ι := Fin 4)
  simp only [Fintype.card_fin] at h
  by_contra hlt
  push Not at hlt
  have : signRank (fun x y : Fin 4 → Bool => x ⬝ᵥ y) ^ 2 ≤ 3 ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  omega

-- Unbounded-error inner product on four bits needs two bits of communication; equality on any
-- finite set needs at most three (`PrivateCoin.uppComplexityFun_equality_le_three`).
example : (2 : ℕ∞) ≤ PrivateCoin.uppComplexityFun (fun x y : Fin 4 → Bool => x ⬝ᵥ y) := by
  simpa using PrivateCoin.card_add_one_div_two_le_uppComplexityFun_dotProduct (ι := Fin 4)

end ForsterTests
