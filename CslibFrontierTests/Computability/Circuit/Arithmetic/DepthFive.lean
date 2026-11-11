/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.LowerBound

/-!
# Homogeneous depth-five circuits

A circuit with two lower product gates `X 0` and `X 1`, two middle sum gates copying them, and
the upper product gates `X 0 * X 1` and `X 1 * X 1`. The second upper product uses the same
middle gate twice. The circuit computes `X 0 * X 1 + X 1 ^ 2` with six gates.

The lower bound for iterated matrix multiplication applies over `ℚ` and over `ℝ`, with one
threshold for both fields.
-/

@[expose] public section

namespace CslibFrontierTests.DepthFive

open Cslib.Circuits.DepthFive MvPolynomial

/-- A circuit for `X 0 * X 1 + X 1 ^ 2` that repeats a middle gate inside a product. -/
def example₁ : Circuit ℚ (Fin 2) where
  lower := 2
  middle := 2
  upper := 2
  degree := 2
  lowerDeg _ := 1
  lowerForms i _ v := if v = i then 1 else 0
  middleDeg _ := 1
  middleCoeff j i := if i = j then 1 else 0
  middle_hom _ _ _ := rfl
  upperArity _ := 2
  upperInputs t a := if a = 0 then t else 1
  outCoeff _ := 1
  out_hom _ _ := rfl

theorem example₁_size : example₁.size = 6 := rfl

theorem example₁_polynomial : example₁.polynomial = X 0 * X 1 + X 1 ^ 2 := by
  change (∑ t : Fin 2, C (1 : ℚ) * ∏ a : Fin 2, ∑ i : Fin 2,
    C (if i = (if a = 0 then t else 1) then (1 : ℚ) else 0) *
      ∏ _ : Fin 1, ∑ v : Fin 2, C (if v = i then (1 : ℚ) else 0) * X v) = _
  simp [Fin.sum_univ_two, Fin.prod_univ_two]
  ring

/-- The circuit certifies that its output `X 0 * X 1 + X 1 ^ 2` is homogeneous of degree `2`. -/
theorem isHomogeneous_example₁ :
    (X 0 * X 1 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ).IsHomogeneous 2 :=
  example₁_polynomial ▸ example₁.isHomogeneous_polynomial

open Cslib.Circuits.Arithmetic in
/-- One threshold serves the rationals and the reals. -/
theorem exists_threshold : ∃ n₀ : ℕ, ∀ (n : ℕ) [NeZero n], n₀ ≤ n →
    (∀ c : Circuit ℚ (Fin n × Fin n × Fin n), c.polynomial = imm ℚ n n →
      (n : ℝ) ^ (√(n : ℝ) / 400) ≤ c.size) ∧
    ∀ c : Circuit ℝ (Fin n × Fin n × Fin n), c.polynomial = imm ℝ n n →
      (n : ℝ) ^ (√(n : ℝ) / 400) ≤ c.size := by
  obtain ⟨n₀, h⟩ := exists_forall_rpow_le_size.{0}
  exact ⟨n₀, fun n _ hn => ⟨h ℚ n hn, h ℝ n hn⟩⟩

end CslibFrontierTests.DepthFive
