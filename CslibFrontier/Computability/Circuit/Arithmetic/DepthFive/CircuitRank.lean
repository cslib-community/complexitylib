/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Model
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.ProductRank
import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.DegreeEstimates

/-!
# The rank measure of a homogeneous depth-five circuit

A homogeneous `ΣΠΣΠΣ` circuit of formal degree `n` with `S₁` lower product gates and `S₃` upper
product gates computes a polynomial of rank measure at most
`2 S₃ max(S₁, 1) D exp (132 √n) n ^ (-√n / 100)`. This is the circuit proposition of
[OpenAI, §3][OpenAI2026DepthFive], whose bound `2 S² D exp (C √n) n ^ (-√n / 100)` in the
number `S` of gates follows from `S₃ max(S₁, 1) ≤ S²`.

The measure is subadditive, so it suffices to bound each upper product gate. If all its factors
have degree less than `n / (4 s)`, the product-rank lemma and the weights of low degrees give
the bound. Otherwise one factor of degree at least `n / (4 s)` is expanded into its lower
product gates. Each resulting product contains at least `n / (4 s)` linear forms, whose weights
give the bound.

## Main results

* `Cslib.Circuits.DepthFive.rankMeasure_upperPoly_le`: the measure of an upper product gate.
* `Cslib.Circuits.DepthFive.rankMeasure_circuit_le`: the measure of a circuit.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §3 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.DepthFive

open MvPolynomial Finset

variable {p : Params} {K σ : Type*} [Field K] [Fintype σ] {s : σ → Prop} [DecidablePred s]

/-- A lower product gate of degree at least `n / (4 s)` times homogeneous polynomials. -/
private theorem rankMeasure_lowerPoly_mul_le (hp : p.Good)
    (hv : Fintype.card {i // s i} = p.v) (hu : Fintype.card {i // ¬ s i} = p.u)
    (c : Circuit K σ) (i : Fin c.lower) {ι : Type*} [Fintype ι] {Q : ι → MvPolynomial σ K}
    {e : ι → ℕ} (hQ : ∀ j, (Q j).IsHomogeneous (e j)) (hd : p.n ≤ 4 * p.s * c.lowerDeg i)
    (he : c.lowerDeg i + ∑ j, e j = p.n) :
    (rankMeasure s (p.k, p.m) (p.a, p.b) (c.lowerPoly i * ∏ j, Q j) : ℝ) ≤
      2 * p.D * (Real.exp (132 * √(p.n : ℝ)) * (p.n : ℝ) ^ (-√(p.n : ℝ) / 100)) := by
  have h := rankMeasure_prod_le hp hv hu (ι := Fin (c.lowerDeg i) ⊕ ι)
    (Q := Sum.elim (fun b => ∑ v, C (c.lowerForms i b v) * X v) Q) (e := Sum.elim (fun _ => 1) e)
    (by rintro (b | j)
        exacts [IsHomogeneous.sum _ _ _ fun v _ => isHomogeneous_C_mul_X _ v, hQ j])
    (by simpa using he)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type] at h
  simp only [Sum.elim_inl, Sum.elim_inr, prod_const, card_univ, Fintype.card_fin] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hp.H_one_pow_mul_prod_H_le hd he) (by positivity))

/-- The rank measure of an upper product gate of degree `n`. -/
theorem rankMeasure_upperPoly_le (hp : p.Good) (hv : Fintype.card {i // s i} = p.v)
    (hu : Fintype.card {i // ¬ s i} = p.u) (c : Circuit K σ) (t : Fin c.upper)
    (ht : ∑ a, c.middleDeg (c.upperInputs t a) = p.n) :
    (rankMeasure s (p.k, p.m) (p.a, p.b) (c.upperPoly t) : ℝ) ≤
      2 * max (c.lower : ℝ) 1 * p.D * Real.exp (132 * √(p.n : ℝ)) *
        (p.n : ℝ) ^ (-√(p.n : ℝ) / 100) := by
  classical
  set B : ℝ := 2 * p.D * (Real.exp (132 * √(p.n : ℝ)) * (p.n : ℝ) ^ (-√(p.n : ℝ) / 100))
  have hB : 0 ≤ B := by positivity
  suffices h : (rankMeasure s (p.k, p.m) (p.a, p.b) (c.upperPoly t) : ℝ) ≤
      max (c.lower : ℝ) 1 * B by
    refine h.trans (le_of_eq ?_)
    simp only [B]
    ring
  by_cases h : ∀ a, 4 * p.s * c.middleDeg (c.upperInputs t a) < p.n
  · calc (rankMeasure s (p.k, p.m) (p.a, p.b) (c.upperPoly t) : ℝ)
        ≤ 2 * p.D * ∏ a, p.H (c.middleDeg (c.upperInputs t a)) :=
          rankMeasure_prod_le hp hv hu (fun a => c.isHomogeneous_middlePoly _) ht
      _ ≤ B := mul_le_mul_of_nonneg_left (hp.prod_H_le_of_low ht h) (by positivity)
      _ ≤ max (c.lower : ℝ) 1 * B := le_mul_of_one_le_left hB (le_max_right _ _)
  · obtain ⟨a₀, ha₀⟩ := not_forall.1 h
    rw [not_lt] at ha₀
    rw [Fintype.sum_eq_add_sum_subtype_ne _ a₀] at ht
    rw [Circuit.upperPoly, Fintype.prod_eq_mul_prod_subtype_ne _ a₀, Circuit.middlePoly,
      sum_mul]
    refine (Nat.cast_le.2 (rankMeasure_sum_le _ _)).trans ?_
    rw [Nat.cast_sum]
    refine (sum_le_sum (g := fun _ => B) fun i _ => ?_).trans ?_
    · by_cases hi : c.middleCoeff (c.upperInputs t a₀) i = 0
      · simpa [hi] using hB
      · have hdeg := c.middle_hom _ i hi
        rw [mul_assoc, C_mul']
        exact (Nat.cast_le.2 (rankMeasure_smul_le _ _)).trans
          (rankMeasure_lowerPoly_mul_le hp hv hu c i
            (fun a => c.isHomogeneous_middlePoly _) (hdeg ▸ ha₀) (hdeg ▸ ht))
    · rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hB

/-- The rank measure of a homogeneous depth-five circuit of degree `n` with `S₁` lower product
gates and `S₃` upper product gates is at most `2 S₃ max(S₁, 1) D exp (132 √n) n ^ (-√n / 100)`. -/
theorem rankMeasure_circuit_le (hp : p.Good) (hv : Fintype.card {i // s i} = p.v)
    (hu : Fintype.card {i // ¬ s i} = p.u) (c : Circuit K σ) (hc : c.degree = p.n) :
    (rankMeasure s (p.k, p.m) (p.a, p.b) c.polynomial : ℝ) ≤
      2 * c.upper * max (c.lower : ℝ) 1 * p.D * Real.exp (132 * √(p.n : ℝ)) *
        (p.n : ℝ) ^ (-√(p.n : ℝ) / 100) := by
  refine (Nat.cast_le.2 (rankMeasure_sum_le _ _)).trans ?_
  rw [Nat.cast_sum]
  refine (sum_le_sum (g := fun _ => 2 * max (c.lower : ℝ) 1 * p.D *
    Real.exp (132 * √(p.n : ℝ)) * (p.n : ℝ) ^ (-√(p.n : ℝ) / 100)) fun t _ => ?_).trans ?_
  · by_cases ht : c.outCoeff t = 0
    · simp only [ht, map_zero, zero_mul, rankMeasure_zero, Nat.cast_zero]
      positivity
    · rw [C_mul']
      exact (Nat.cast_le.2 (rankMeasure_smul_le _ _)).trans
        (rankMeasure_upperPoly_le hp hv hu c t ((c.out_hom t ht).trans hc))
  · rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_eq (by ring)

end Cslib.Circuits.DepthFive
