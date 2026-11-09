/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.WidePolynomialSetup

/-!
# Pulling a wide polynomial back to square matrices

For a nonnegative row-stochastic `B`, substitution along `W ↦ W * B`
produces an actual square `MvPolynomial`.  Its DPI and outer-product RKO
properties are inherited from the wide polynomial.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`WideSquarePullback.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators

namespace WidePolynomial

open GeneralAsymmetricC1

/-- A nonnegative rectangular matrix whose rows sum to one. -/
@[expose] def RowStochastic {n m : ℕ} (B : Mat n m) : Prop :=
  (∀ i a, 0 ≤ B i a) ∧ (∀ i, ∑ a, B i a = 1)

/-- An entry of the generic square matrix multiplied by a fixed rectangular matrix. -/
def rightPullbackEntry {n m : ℕ} (B : Mat n m)
    (ia : WideVar n m) : SquarePolynomial.Poly n :=
  ∑ j : Fin n,
    MvPolynomial.X (ia.1, j) * MvPolynomial.C (B j ia.2)

/-- Substitute right multiplication by a fixed rectangular matrix into an entry polynomial. -/
@[expose] def rightPullbackPoly {n m : ℕ} (P : WidePoly n m) (B : Mat n m) :
    SquarePolynomial.Poly n :=
  MvPolynomial.eval₂ MvPolynomial.C (rightPullbackEntry B) P

lemma peval_rightPullbackPoly {n m : ℕ}
    (P : WidePoly n m) (B : Mat n m) (W : Mat n n) :
    SquarePolynomial.peval (rightPullbackPoly P B) W = peval P (W * B) := by
  unfold rightPullbackPoly SquarePolynomial.peval peval
  rw [MvPolynomial.eval_eval₂]
  simp only [MvPolynomial.eval_C,
    rightPullbackEntry, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_X]
  rw [← MvPolynomial.eval₂_id]
  apply MvPolynomial.eval₂Hom_congr
  · ext r
    simp
  · funext ia
    rfl
  · rfl

lemma right_mul_nonnegative {n m : ℕ} {W : Mat n n} {B : Mat n m}
    (hW : Nonnegative W) (hB : RowStochastic B) :
    Nonnegative (W * B) := by
  intro i a
  rw [mat_mul_apply]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hW i j) (hB.1 j a)

lemma right_mul_mass {n m : ℕ} (W : Mat n n) {B : Mat n m}
    (hB : RowStochastic B) :
    mass (W * B) = mass W := by
  unfold mass
  simp only [mat_mul_apply]
  calc
    (∑ i, ∑ a, ∑ j, W i j * B j a) =
        ∑ i, ∑ j, ∑ a, W i j * B j a := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, W i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum, hB.2 j, mul_one]

lemma right_mul_simplex {n m : ℕ} {W : Mat n n} {B : Mat n m}
    (hW : Simplex W) (hB : RowStochastic B) :
    Simplex (W * B) := by
  exact ⟨right_mul_nonnegative hW.1 hB,
    (right_mul_mass W hB).trans hW.2⟩

lemma mat_mul_assoc_wide {n p m : ℕ}
    (A : Mat n n) (W : Mat n p) (B : Mat p m) :
    (A * W) * B = A * (W * B) := by
  ext i a
  simp only [mat_mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

lemma outer_mul_right {n m : ℕ}
    (x y : Fin n → ℝ) (B : Mat n m) :
    outer x y * B = outer x (fun a => ∑ j, y j * B j a) := by
  ext i a
  simp [outer, mat_mul_apply, Finset.mul_sum, mul_assoc]

theorem rightPullback_polynomialDPI {n m : ℕ}
    (P : WidePoly n m) {B : Mat n m} (hB : RowStochastic B)
    (hDPI : PolynomialDPI P) :
    SquarePolynomial.PolynomialDPI (rightPullbackPoly P B) := by
  intro T W hT hW
  rw [peval_rightPullbackPoly, peval_rightPullbackPoly,
    mat_mul_assoc_wide]
  exact hDPI T (W * B) hT (right_mul_simplex hW hB)

theorem rightPullback_polynomialRKO {n m : ℕ}
    (P : WidePoly n m) {B : Mat n m} (hB : RowStochastic B)
    (hRKO : PolynomialRKO P) :
    SquarePolynomial.PolynomialRKO (rightPullbackPoly P B) := by
  intro x y hxy
  rw [peval_rightPullbackPoly, outer_mul_right]
  have hsimplex := right_mul_simplex hxy hB
  rw [outer_mul_right] at hsimplex
  exact hRKO x (fun a => ∑ j, y j * B j a) hsimplex

end WidePolynomial

end

end Cslib.FiniteSampleInformation
