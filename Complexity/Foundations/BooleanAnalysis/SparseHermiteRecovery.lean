/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseReplacementDesign
public import Complexity.Foundations.Combinatorics.ReplacementDesignBridge
public import Complexity.Foundations.Data.MvPolynomial.AffineTaylor
public import Complexity.Foundations.Data.Polynomial.StagedJetArithmetic

/-!
# Measurement-fiber Taylor-jet identities and Hermite–Cramer zero-counting recovery

This module completes two mathematical bridges in the polynomial-interpolation and parity-counting
pipeline of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (Sections 3.4,
5.3–5.5, and Appendix B.2–B.3, printed pp. 24–25, 37–39, 48–50):

1. **§3.4 Affine-Taylor to measurement-fiber jet bridge (`Cslib.ReplacementCounting`, equations
   (3.9)–(3.13) and Proposition 3.4, pp. 24–25)**:
   Connecting `Cslib.AffineTaylor` (`replacedSum`, `affineInput`, `affineFactor`, `factorProduct`,
   `coeff_taylor_replacedSum_eq_restricted_subsets`) with `Cslib.ReplacementCounting.Design`
   (`targetPoly`, `shiftedFactorEval`, `sum_restricted_shiftedFactor_eq_sum_measurement_fibers`):
   - `targetPolynomial_eq_replacedSum` and `Design.targetPoly_eq_replacedSum` identify
     `targetPolynomial` with `AffineTaylor.replacedSum`.
   - `Design.map_eval_affineInput_indicator`, `Design.map_eval_affineFactor_indicator`, and
     `Design.eval_coeff_factorProduct_indicator` show that evaluating the formal Boolean variables
     `X` of `AffineTaylor.affineFactor` and `AffineTaylor.factorProduct` at the subset indicator of
     `U ⊆ ι` produces `M.shiftedFactorEval Φ t U`.
   - `Design.coeff_taylor_targetPoly_eq_sum_measurement_fibers` and
     `Design.coeff_taylor_targetPoly_eq_measurementFiberJet` prove **equation (3.13)**: for every
     jet order `j ≤ q` at evaluation node `t : Fin Q`, `[z ^ j] H(t + z)` equals the signed Möbius
     sum over subset pairs `#E ≤ q`, `U ⊆ E` of the measurement-fiber sums over
     `M.measurementBox t`.
   - `Design.targetSum_eq_of_measurementFiberJet` and
     `Design.targetSum_eq_of_measurementFiberJet_jetOrder` combine equation (3.13) with confluent
     Hermite interpolation (`Design.targetSum_eq_of_taylorJet_jetOrder`) to recover
     `targetSum s scope Φ` directly from `M.measurementFiberJet`.

2. **§5.4 & Appendix B.2–B.3 Taylor-shift commutation, `JetTable` bridge, and unconditional
   Hermite–Cramer recovery (`Cslib.BitString`, pp. 37–39, 48–50)**:
   - **Taylor-shift commutation**: `Polynomial.taylor t` commutes with `clearedMonomialPoly`,
     `clearedMonomialSumPoly`, `parityBaseDigitCleared`, `hPolyCleared`, `parityFactorCleared`,
     `univariateClearedParityCoord`, and `univariateClearedParityTruncatedSum` by shifting each
     variable numerator polynomial `θ x i v` (`taylor_univariateClearedParityCoord`,
     `taylor_univariateClearedParityTruncatedSum`).
   - **Staged `JetTable` bridge (Appendix B.2)**: `JetTable.ofPolyVPolyZ J ℓ` extracts the `(J × ℓ)`
     coefficient table `(j, u) ↦ [z ^ j] ([V ^ u] Q)` as a ring homomorphism
     `Polynomial (Polynomial R) →+* JetTable J ℓ R`. Under `ofPolyVPolyZ J ℓ`, the Stage-1 and
     Stage-2 table operations `JetTable.clearedMonomialJet`, `JetTable.clearedMonomialSumJet`, and
     `JetTable.clearedParityFactorJet` from `StagedJetArithmetic` compute the exact Taylor-jet
     coefficients of `clearedMonomialSumPoly`, `parityFactorCleared`, and
     `univariateClearedParityCoord` (`clearedParityJetTable_apply`).
   - **Unconditional Hermite–Cramer determinant recovery (Appendix B.3, eq. B.1)**:
     instantiating `Polynomial.hermiteMatrix` and `Cslib.hermiteCramerNumerator` at distinct integer
     nodes `nodes : Fin Q → ℤ` (and at `nodeInt : Fin Q → ℤ` with canonical jet order
     `sparseParityJetOrder k R Q #I ℓ` for any `D : ReplacementDesign scope Q r A₀ R τ`) discharges
     the abstract `D_H ≠ 0` and `hcramer` premises of `emod_sum_cramer_ediv_eq_commonZeroCount` and
     `emod_sum_cramer_ediv_design_eq_commonZeroCount` unconditionally
     (`emod_sum_hermiteCramerNumerator_ediv_eq_commonZeroCount`,
     `emod_sum_hermiteCramerNumerator_design_eq_commonZeroCount`,
     `emod_hermiteCramerNumerator_truncatedSum_design_eq_commonZeroCount`, and branch-summed
     `commonZeroCount_eq_sum_branch_hermiteCramerNumerator_design`).

## Main definitions

* `Cslib.ReplacementCounting.Design.measurementFiberJet`: the equation (3.13) Möbius-summed
  measurement-fiber Taylor-jet coefficient at node `t` and order `j`.
* `Cslib.BitString.clearedParityJetTable`: `(J × ℓ)` integer jet table at evaluation point `t : ℤ`
  built from `JetTable.clearedParityFactorJet` and `JetTable.clearedMonomialSumJet`.
* `Cslib.BitString.sparseParityJetOrder`: canonical confluent jet order
  `ReplacementCounting.jetOrder ((k * (R - 1)) * (m_eq + 2 * (ℓ - 1))) Q`.

## Main results

* `Cslib.ReplacementCounting.targetPolynomial_eq_replacedSum`,
  `Cslib.ReplacementCounting.Design.map_eval_affineFactor_indicator`,
  `Cslib.ReplacementCounting.Design.coeff_taylor_targetPoly_eq_sum_measurement_fibers`,
  `Cslib.ReplacementCounting.Design.targetSum_eq_of_measurementFiberJet_jetOrder`:
  §3.4 equation (3.13) and Proposition 3.4 measurement-fiber Taylor-jet recovery.
* `Cslib.BitString.taylor_univariateClearedParityCoord`,
  `Cslib.BitString.taylor_univariateClearedParityTruncatedSum`,
  `Cslib.BitString.clearedParityJetTable_apply`:
  Taylor-shift commutation and exact `JetTable` correspondence for cleared parity polynomials.
* `Cslib.BitString.hermiteCramerNumerator_intPoly_eq_mul`,
  `Cslib.BitString.emod_sum_hermiteCramerNumerator_ediv_eq_commonZeroCount`,
  `Cslib.BitString.emod_sum_hermiteCramerNumerator_design_eq_commonZeroCount`,
  `Cslib.BitString.emod_hermiteCramerNumerator_truncatedSum_design_eq_commonZeroCount`,
  `Cslib.BitString.commonZeroCount_eq_sum_branch_hermiteCramerNumerator_design`:
  unconditional Hermite–Cramer determinant recovery of `commonZeroCount`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §3.4, §§5.3–5.5, and
  Appendix B.2–B.3, pp. 24–25, 37–39, 48–50.
-/

@[expose] public noncomputable section

open Finset Polynomial
open scoped BigOperators

/-! ### 1. §3.4 Affine-Taylor to measurement-fiber jet bridge (equations (3.9)–(3.13)) -/

namespace Cslib.ReplacementCounting

/-- `ReplacementCounting.targetPolynomial` coincides with `AffineTaylor.replacedSum`
([OpenAI2026ETH], equation (3.3), pp. 21, 24). -/
theorem targetPolynomial_eq_replacedSum {ι F A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] {κ : F → Type*} (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A) :
    targetPolynomial s Φ P = Cslib.AffineTaylor.replacedSum s Φ P := by
  unfold targetPolynomial Cslib.AffineTaylor.replacedSum replacementEval
  exact sum_congr (Finset.ext fun _ => by simp only [mem_univ]) fun x _ =>
    prod_congr rfl fun f _ => rfl

namespace Design

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] {s : Finset F} {κ : F → Type*}
  {scope : ∀ f, κ f → ι} {r Q R D : ℕ} {τ : ℝ}
  (M : Design ι s κ scope r Q R D τ)

/-- `M.targetPoly Φ` coincides with `AffineTaylor.replacedSum s Φ (M.rowIn A)`. -/
theorem targetPoly_eq_replacedSum {A : Type*} [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) :
    M.targetPoly Φ = Cslib.AffineTaylor.replacedSum s Φ (M.rowIn A) :=
  targetPolynomial_eq_replacedSum s Φ (M.rowIn A)

/-- Evaluating the formal variables `X` of `AffineTaylor.affineInput (M.rowIn A f v)` at the
indicator of `U ⊆ ι` yields the scalar baseline `algebraMap ℚ A (M.evalRow t f v x)` plus the sum
of Taylor corrections over `i ∈ U` ([OpenAI2026ETH], equations (3.7)–(3.8), p. 24). -/
theorem map_eval_affineInput_indicator {A : Type*} [CommRing A] [Algebra ℚ A]
    (t : Fin Q) (U : Finset ι) (f : F) (v : κ f) (x : ι → Bool) :
    (Cslib.AffineTaylor.affineInput (M.rowIn A f v) (M.nodes t : A) x).map
        (MvPolynomial.eval fun i => BitString.bitVal A (decide (i ∈ U))) =
      Polynomial.C (algebraMap ℚ A (M.evalRow t f v x)) +
        ∑ i ∈ U, (Polynomial.taylor (M.nodes t : A) (M.rowIn A f v i) -
          Polynomial.C ((M.rowIn A f v i).eval (M.nodes t : A))) := by
  rw [Cslib.AffineTaylor.map_eval_affineInput]
  congr 1
  · congr 1
    have hbit : ∀ b : Bool, BitString.bitVal A b = algebraMap ℚ A (BitString.bitVal ℚ b) := by
      rintro (_ | _) <;>
        simp only [BitString.bitVal_false, BitString.bitVal_true, map_zero, map_one]
    simp only [evalRow, evalRowRat, map_sum, map_mul, ← hbit, rowIn]
    refine sum_congr rfl fun i _ => ?_
    have hnode : (M.nodes t : A) = algebraMap ℚ A (M.nodes t : ℚ) := by simp only [map_intCast]
    rw [hnode, Polynomial.eval_map_apply]
  · rw [← sum_subset (subset_univ U)]
    · refine sum_congr rfl fun i hi => ?_
      simp only [decide_eq_true_eq.mpr hi, BitString.bitVal_true, Polynomial.C_1, one_mul]
    · intro i _ hi
      simp only [decide_eq_false_iff_not.mpr hi, BitString.bitVal_false, Polynomial.C_0, zero_mul]

/-- Evaluating the formal variables `X` of `AffineTaylor.affineFactor` at the indicator of `U ⊆ ι`
produces `M.shiftedFactorEval Φ t U f (fun v => M.evalRow t f v x)` ([OpenAI2026ETH],
equations (3.8) and (3.11), pp. 24–25). -/
theorem map_eval_affineFactor_indicator {A : Type*} [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) (t : Fin Q) (U : Finset ι) (f : F) (x : ι → Bool) :
    (Cslib.AffineTaylor.affineFactor (Φ f) (M.rowIn A f) (M.nodes t : A) x).map
        (MvPolynomial.eval fun i => BitString.bitVal A (decide (i ∈ U))) =
      M.shiftedFactorEval Φ t U f (fun v => M.evalRow t f v x) := by
  rw [Cslib.AffineTaylor.map_eval_affineFactor, shiftedFactorEval, MvPolynomial.aeval_def]
  congr 1
  funext v
  exact M.map_eval_affineInput_indicator t U f v x

/-- Evaluating the `j`-th Taylor coefficient of `AffineTaylor.factorProduct` at the indicator of
`U ⊆ ι` equals the `j`-th coefficient of the product of `M.shiftedFactorEval` over `f ∈ s`. -/
theorem eval_coeff_factorProduct_indicator {A : Type*} [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) (t : Fin Q) (U : Finset ι) (x : ι → Bool) (j : ℕ) :
    MvPolynomial.eval (fun i => BitString.bitVal A (decide (i ∈ U)))
        ((Cslib.AffineTaylor.factorProduct s Φ (M.rowIn A) (M.nodes t : A) x).coeff j) =
      (∏ f ∈ s, M.shiftedFactorEval Φ t U f (fun v => M.evalRow t f v x)).coeff j := by
  rw [Cslib.AffineTaylor.eval_coeff_factorProduct]
  refine congrArg (fun p : Polynomial A => p.coeff j) (prod_congr rfl fun f _ => ?_)
  exact M.map_eval_affineFactor_indicator Φ t U f x

/-- Classical fiber-representative selector for `M.localMeasure t`, choosing a local Boolean
assignment `u : M.LocalCube t g` with `M.localMeasure t g u = y g` whenever all fibers `y g` are
nonempty. -/
def classicalRepresentative (t : Fin Q)
    (y : ∀ g : Fin r, Fin (M.numRows t g) → ℤ)
    (hy : ∀ g, ∃ u : M.LocalCube t g, M.localMeasure t g u = y g)
    (g : Fin r) : M.LocalCube t g :=
  Classical.choose (hy g)

/-- `M.classicalRepresentative t` satisfies the representative validity condition for
`SharedSummaries.fiberContribution`. -/
theorem classicalRepresentative_valid (t : Fin Q)
    (y : ∀ g : Fin r, Fin (M.numRows t g) → ℤ)
    (hy : ∀ g, ∃ u : M.LocalCube t g, M.localMeasure t g u = y g) (g : Fin r) :
    M.localMeasure t g (M.classicalRepresentative t y hy g) = y g :=
  Classical.choose_spec (hy g)

/-- **Equation (3.13) measurement-fiber Taylor-jet coefficient** ([OpenAI2026ETH], §3.4, p. 25):
the signed Möbius sum over subset pairs `E ⊆ ι` (`#E ≤ q`) and `U ⊆ E` of the `j`-th coefficient of
the measurement-fiber sum at node `t : Fin Q`. -/
def measurementFiberJet {A : Type*} [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) (q : ℕ) (t : Fin Q)
    (representative : ∀ y : ∀ g : Fin r, Fin (M.numRows t g) → ℤ,
      (∀ g, ∃ u : M.LocalCube t g, M.localMeasure t g u = y g) → ∀ g, M.LocalCube t g)
    (j : ℕ) : A :=
  ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
    ∑ U ∈ E.powerset, (-1 : A) ^ (#E - #U) *
      ∑ y ∈ M.measurementBox t,
        (SharedSummaries.fiberContribution (M.localMeasure t) (M.restrictedLocalCube t E)
          (M.groupedFactor (M.shiftedFactorEval Φ t U) t) representative y).coeff j

/-- **Equation (3.13) Taylor-jet measurement-fiber identity** ([OpenAI2026ETH], §3.4, pp. 24–25):
for every Taylor order `j ≤ q` and node `t : Fin Q`, `[z ^ j] H(nodes t + z)` equals the signed
Möbius sum over `#E ≤ q` and `U ⊆ E` of the `j`-th coefficient of the measurement-fiber sums over
`M.measurementBox t`. -/
theorem coeff_taylor_targetPoly_eq_sum_measurement_fibers {A : Type*} [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) (t : Fin Q) {j q : ℕ} (hj : j ≤ q)
    (representative : ∀ y : ∀ g : Fin r, Fin (M.numRows t g) → ℤ,
      (∀ g, ∃ u : M.LocalCube t g, M.localMeasure t g u = y g) → ∀ g, M.LocalCube t g)
    (valid : ∀ y hy g, M.localMeasure t g (representative y hy g) = y g) :
    (Polynomial.taylor (M.nodes t : A) (M.targetPoly Φ)).coeff j =
      ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
        ∑ U ∈ E.powerset, (-1 : A) ^ (#E - #U) *
          ∑ y ∈ M.measurementBox t,
            (SharedSummaries.fiberContribution (M.localMeasure t) (M.restrictedLocalCube t E)
              (M.groupedFactor (M.shiftedFactorEval Φ t U) t) representative y).coeff j := by
  rw [M.targetPoly_eq_replacedSum Φ,
    Cslib.AffineTaylor.coeff_taylor_replacedSum_eq_restricted_subsets s Φ (M.rowIn A)
      (M.nodes t : A) hj]
  refine sum_congr rfl fun E _ => sum_congr rfl fun U _ => ?_
  congr 1
  rw [← Polynomial.finsetSum_coeff,
    ← M.sum_restricted_shiftedFactor_eq_sum_measurement_fibers Φ t E U representative valid,
    Polynomial.finsetSum_coeff]
  refine sum_congr (Finset.ext fun _ => by simp only [mem_filter, mem_univ, true_and]) fun x _ => ?_
  rw [← M.eval_coeff_factorProduct_indicator Φ t U x j]
  congr!

/-- Packaging `coeff_taylor_targetPoly_eq_sum_measurement_fibers` in terms of
`M.measurementFiberJet`. -/
theorem coeff_taylor_targetPoly_eq_measurementFiberJet {A : Type*} [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) (t : Fin Q) {j q : ℕ} (hj : j ≤ q)
    (representative : ∀ y : ∀ g : Fin r, Fin (M.numRows t g) → ℤ,
      (∀ g, ∃ u : M.LocalCube t g, M.localMeasure t g u = y g) → ∀ g, M.LocalCube t g)
    (valid : ∀ y hy g, M.localMeasure t g (representative y hy g) = y g) :
    (Polynomial.taylor (M.nodes t : A) (M.targetPoly Φ)).coeff j =
      M.measurementFiberJet Φ q t representative j :=
  M.coeff_taylor_targetPoly_eq_sum_measurement_fibers Φ t hj representative valid

/-- When `J ≤ q + 1`, the order-`J` Taylor jet `Polynomial.taylorJet` of `M.targetPoly Φ` at
`M.nodes` agrees entrywise with `M.measurementFiberJet Φ q`. -/
theorem taylorJet_targetPoly_eq_measurementFiberJet {A : Type*} [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) {J q : ℕ} (hJq : J ≤ q + 1)
    (representative : ∀ t : Fin Q, ∀ y : ∀ g : Fin r, Fin (M.numRows t g) → ℤ,
      (∀ g, ∃ u : M.LocalCube t g, M.localMeasure t g u = y g) → ∀ g, M.LocalCube t g)
    (valid : ∀ t y hy g, M.localMeasure t g (representative t y hy g) = y g) :
    Polynomial.taylorJet (fun t => (M.nodes t : A)) J (M.targetPoly Φ) =
      fun p : Fin Q × Fin J => M.measurementFiberJet Φ q p.1 (representative p.1) p.2.1 := by
  funext p
  rw [Polynomial.taylorJet_apply]
  exact M.coeff_taylor_targetPoly_eq_measurementFiberJet Φ p.1
    (Nat.le_of_lt_succ (lt_of_lt_of_le p.2.2 hJq)) (representative p.1) (valid p.1)

/-- **Proposition 3.4 complete algebraic recovery of `targetSum` from measurement-fiber Taylor
jets** ([OpenAI2026ETH], §§3.4–3.5, pp. 24–25): whenever
`(liftedFactorProduct s Φ).totalDegree ≤ d`, `0 < J`, `d * R < Q * J`, and `J ≤ q + 1`,
`targetSum s scope Φ` equals the Hermite determinant formed from `M.measurementFiberJet Φ q`. -/
theorem targetSum_eq_of_measurementFiberJet (A : Type*) [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) {d J q : ℕ}
    (hd : (liftedFactorProduct s Φ).totalDegree ≤ d)
    (hJ : 0 < J) (hQJ : d * R < Q * J) (hJq : J ≤ q + 1)
    (representative : ∀ t : Fin Q, ∀ y : ∀ g : Fin r, Fin (M.numRows t g) → ℤ,
      (∀ g, ∃ u : M.LocalCube t g, M.localMeasure t g u = y g) → ∀ g, M.LocalCube t g)
    (valid : ∀ t y hy g, M.localMeasure t g (representative t y hy g) = y g) :
    targetSum s scope Φ = ((Polynomial.hermiteMatrix M.nodes J).det : ℚ)⁻¹ •
      (((Polynomial.hermiteMatrix M.nodes J).map (Int.cast : ℤ → A)).updateCol
        (⟨0, M.Q_pos⟩, ⟨0, hJ⟩)
        (fun p => M.measurementFiberJet Φ q p.1 (representative p.1) p.2.1)).det := by
  rw [M.targetSum_eq_of_taylorJet A Φ hd hJ hQJ,
    M.taylorJet_targetPoly_eq_measurementFiberJet Φ hJq representative valid]

/-- Specialization of `targetSum_eq_of_measurementFiberJet` to the canonical truncation order
`q = (d * R) / Q` and jet order `J = jetOrder (d * R) Q = (d * R) / Q + 1`
([OpenAI2026ETH], equation (3.5) and Proposition 3.4, pp. 24–25). -/
theorem targetSum_eq_of_measurementFiberJet_jetOrder (A : Type*) [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) {d : ℕ}
    (hd : (liftedFactorProduct s Φ).totalDegree ≤ d)
    (representative : ∀ t : Fin Q, ∀ y : ∀ g : Fin r, Fin (M.numRows t g) → ℤ,
      (∀ g, ∃ u : M.LocalCube t g, M.localMeasure t g u = y g) → ∀ g, M.LocalCube t g)
    (valid : ∀ t y hy g, M.localMeasure t g (representative t y hy g) = y g) :
    targetSum s scope Φ =
      ((Polynomial.hermiteMatrix M.nodes (jetOrder (d * R) Q)).det : ℚ)⁻¹ •
        (((Polynomial.hermiteMatrix M.nodes (jetOrder (d * R) Q)).map
          (Int.cast : ℤ → A)).updateCol (⟨0, M.Q_pos⟩, ⟨0, jetOrder_pos _ _⟩)
          (fun p => M.measurementFiberJet Φ ((d * R) / Q) p.1
            (representative p.1) p.2.1)).det :=
  M.targetSum_eq_of_measurementFiberJet A Φ hd (jetOrder_pos _ _)
    (lt_mul_jetOrder (d * R) M.Q_pos) le_rfl representative valid

end Design

end Cslib.ReplacementCounting

/-! ### 2. §5.4 & Appendix B.2–B.3 Taylor-shift commutation, `JetTable` bridge, and unconditional
Hermite–Cramer recovery -/

namespace Cslib.BitString

open Cslib.LinearAlgebra

variable {ι κ : Type*}

/-! #### 3.1 Taylor-shift commutation with cleared parity polynomials -/

/-- `Polynomial.taylor t` commutes with `clearedMonomialPoly` by Taylor-shifting each factor
`θ v`. -/
theorem taylor_clearedMonomialPoly (t d_den : ℤ) (k : ℕ) (θ : ι → Polynomial ℤ) (M : Finset ι) :
    Polynomial.taylor t (clearedMonomialPoly d_den k θ M) =
      clearedMonomialPoly d_den k (fun v => Polynomial.taylor t (θ v)) M := by
  unfold clearedMonomialPoly
  rw [← Polynomial.taylorAlgHom_apply, map_mul, map_prod]
  simp only [Polynomial.taylorAlgHom_apply, Polynomial.taylor_C]

/-- `Polynomial.taylor t` commutes with `clearedMonomialSumPoly` by Taylor-shifting each factor
`θ v`. -/
theorem taylor_clearedMonomialSumPoly (t d_den : ℤ) (k : ℕ) (θ : ι → Polynomial ℤ)
    (𝓜 : Finset (Finset ι)) :
    Polynomial.taylor t (clearedMonomialSumPoly d_den k θ 𝓜) =
      clearedMonomialSumPoly d_den k (fun v => Polynomial.taylor t (θ v)) 𝓜 := by
  unfold clearedMonomialSumPoly
  rw [map_sum]
  exact sum_congr rfl fun M _ => taylor_clearedMonomialPoly t d_den k θ M

/-- Mapping `parityFactorCleared ℓ (Polynomial.C Δ) A_i` by `(Polynomial.taylorAlgHom t).toRingHom`
shifts `A_i` by `Polynomial.taylor t`. -/
theorem map_taylor_parityFactorCleared {R : Type*} [CommRing R] (t Δ : R) (ℓ : ℕ)
    (A_i : Polynomial R) :
    (parityFactorCleared ℓ (Polynomial.C Δ) A_i).map (Polynomial.taylorAlgHom t).toRingHom =
      parityFactorCleared ℓ (Polynomial.C Δ) (Polynomial.taylor t A_i) := by
  have hhom := map_parityFactorCleared (Polynomial.taylorAlgHom t).toRingHom ℓ (Polynomial.C Δ) A_i
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.taylorAlgHom_apply,
    Polynomial.taylor_C] using hhom

/-- `Polynomial.taylor t` commutes with `univariateClearedParityCoord` by Taylor-shifting each
numerator polynomial `θ x i v`. -/
theorem taylor_univariateClearedParityCoord [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (t d_den : ℤ) (k ℓ : ℕ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) (s : ℕ) :
    Polynomial.taylor t (univariateClearedParityCoord I P d_den k ℓ θ s) =
      univariateClearedParityCoord I P d_den k ℓ
        (fun x i v => Polynomial.taylor t (θ x i v)) s := by
  rw [univariateClearedParityCoord_eq_sum, univariateClearedParityCoord_eq_sum, map_sum]
  refine sum_congr rfl fun x _ => ?_
  have hcoeff :
      Polynomial.taylor t
          ((∏ i ∈ I,
            parityFactorCleared ℓ (Polynomial.C (d_den ^ k))
              (clearedMonomialSumPoly d_den k (θ x i) (P i))).coeff s) =
        (((∏ i ∈ I,
            parityFactorCleared ℓ (Polynomial.C (d_den ^ k))
              (clearedMonomialSumPoly d_den k (θ x i) (P i))).map
                (Polynomial.taylorAlgHom t).toRingHom).coeff s) := by
    rw [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.taylorAlgHom_apply]
  rw [hcoeff, Polynomial.map_prod]
  refine congrArg (fun Q : Polynomial (Polynomial ℤ) => Q.coeff s) (prod_congr rfl fun i _ => ?_)
  rw [map_taylor_parityFactorCleared, taylor_clearedMonomialSumPoly]

/-- `Polynomial.taylor t` commutes with `univariateClearedParityTruncatedSum` by Taylor-shifting
each numerator polynomial `θ x i v`. -/
theorem taylor_univariateClearedParityTruncatedSum [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (t d_den : ℤ) (k ℓ : ℕ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) :
    Polynomial.taylor t (univariateClearedParityTruncatedSum I P d_den k ℓ θ) =
      univariateClearedParityTruncatedSum I P d_den k ℓ
        (fun x i v => Polynomial.taylor t (θ x i v)) := by
  rw [univariateClearedParityTruncatedSum_eq_sum_coord,
    univariateClearedParityTruncatedSum_eq_sum_coord, map_sum]
  exact sum_congr rfl fun s _ => taylor_univariateClearedParityCoord I P t d_den k ℓ θ s

/-! #### 3.2 Exact correspondence with `JetTable` staged operations (Appendix B.2) -/

/-- `JetTable.ofPolyZ J ℓ` maps `clearedMonomialPoly d_den k θ M` to
`JetTable.clearedMonomialJet d_den k (fun v => JetTable.ofPolyZ J ℓ (θ v)) M`. -/
theorem ofPolyZ_clearedMonomialPoly (J ℓ : ℕ) (d_den : ℤ) (k : ℕ) (θ : ι → Polynomial ℤ)
    (M : Finset ι) :
    JetTable.ofPolyZ J ℓ (clearedMonomialPoly d_den k θ M) =
      JetTable.clearedMonomialJet d_den k (fun v => JetTable.ofPolyZ J ℓ (θ v)) M := by
  unfold clearedMonomialPoly JetTable.clearedMonomialJet
  rw [map_mul, map_prod, JetTable.ofPolyZ_C, JetTable.zsmul_eq_const_mul, Int.cast_id]

/-- `JetTable.ofPolyZ J ℓ` maps `clearedMonomialSumPoly d_den k θ 𝓜` to
`JetTable.clearedMonomialSumJet d_den k (fun v => JetTable.ofPolyZ J ℓ (θ v)) 𝓜 id`. -/
theorem ofPolyZ_clearedMonomialSumPoly (J ℓ : ℕ) (d_den : ℤ) (k : ℕ) (θ : ι → Polynomial ℤ)
    (𝓜 : Finset (Finset ι)) :
    JetTable.ofPolyZ J ℓ (clearedMonomialSumPoly d_den k θ 𝓜) =
      JetTable.clearedMonomialSumJet d_den k (fun v => JetTable.ofPolyZ J ℓ (θ v)) 𝓜 id := by
  unfold clearedMonomialSumPoly JetTable.clearedMonomialSumJet
  rw [map_sum]
  exact sum_congr rfl fun M _ => ofPolyZ_clearedMonomialPoly J ℓ d_den k θ M

/-- `JetTable.ofPolyVPolyZ J ℓ` maps `parityFactorCleared ℓ (Polynomial.C Δ) A_i` to
`JetTable.clearedParityFactorJet Δ (JetTable.ofPolyZ J ℓ A_i)` with coefficients from
`Polynomial.parityBaseDigit ℓ`. -/
theorem ofPolyVPolyZ_parityFactorCleared (J ℓ : ℕ) (Δ : ℤ) (A_i : Polynomial ℤ) :
    JetTable.ofPolyVPolyZ J ℓ (parityFactorCleared ℓ (Polynomial.C Δ) A_i) =
      JetTable.clearedParityFactorJet Δ (JetTable.ofPolyZ J ℓ A_i)
        (fun s => (Polynomial.parityBaseDigit ℓ s).coeff 0)
        (fun s => (Polynomial.parityBaseDigit ℓ s).coeff 1) := by
  unfold parityFactorCleared JetTable.clearedParityFactorJet
  rw [map_sum, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun s _ => ?_
  have hdigit :
      JetTable.ofPolyZ J ℓ (parityBaseDigitCleared ℓ (s : ℕ) (Polynomial.C Δ) A_i) =
        ((Polynomial.parityBaseDigit ℓ (s : ℕ)).coeff 0) • JetTable.const Δ +
          ((Polynomial.parityBaseDigit ℓ (s : ℕ)).coeff 1) • JetTable.ofPolyZ J ℓ A_i := by
    unfold parityBaseDigitCleared
    rw [map_add, map_mul, map_mul, map_intCast, map_intCast, JetTable.ofPolyZ_C,
      zsmul_eq_mul, zsmul_eq_mul]
  have hhpoly :
      JetTable.ofPolyZ J ℓ (hPolyCleared (Polynomial.C Δ) A_i) =
        JetTable.ofPolyZ J ℓ A_i * (JetTable.ofPolyZ J ℓ A_i - JetTable.const Δ) := by
    unfold hPolyCleared
    rw [map_mul, map_sub, JetTable.ofPolyZ_C]
  rw [map_mul, JetTable.ofPolyVPolyZ_C, JetTable.ofPolyVPolyZ_X_pow, map_mul, map_mul,
    map_pow, map_pow, JetTable.ofPolyZ_C, hdigit, hhpoly,
    JetTable.zsmul_eq_const_mul (Δ ^ (2 * (ℓ - 1 - (s : ℕ)))), Int.cast_id, ← JetTable.const_pow]
  simp only [mul_assoc]

/-- The `(J × ℓ)` integer Taylor-jet table at evaluation point `t : ℤ` constructed from the Stage-1
and Stage-2 `JetTable` operations (`JetTable.clearedMonomialSumJet` and
`JetTable.clearedParityFactorJet`) of `StagedJetArithmetic` ([OpenAI2026ETH], Appendix B.2,
pp. 48–49). -/
def clearedParityJetTable [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (d_den : ℤ) (k ℓ J : ℕ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) (t : ℤ) : JetTable J ℓ ℤ :=
  ∑ x : ι → Bool,
    ∏ i ∈ I,
      JetTable.clearedParityFactorJet (d_den ^ k)
        (JetTable.clearedMonomialSumJet d_den k
          (fun v => JetTable.ofPolyZ J ℓ (Polynomial.taylor t (θ x i v))) (P i) id)
        (fun s => (Polynomial.parityBaseDigit ℓ s).coeff 0)
        (fun s => (Polynomial.parityBaseDigit ℓ s).coeff 1)

/-- **Appendix B.2 `JetTable` Taylor-jet identity**: at every jet order `j : Fin J` and `V`-degree
`s : Fin ℓ`, `clearedParityJetTable I P d_den k ℓ J θ t j s` equals the `j`-th Taylor coefficient of
`univariateClearedParityCoord I P d_den k ℓ θ s` at `t`. -/
theorem clearedParityJetTable_apply [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (d_den : ℤ) (k ℓ J : ℕ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) (t : ℤ) (j : Fin J) (s : Fin ℓ) :
    clearedParityJetTable I P d_den k ℓ J θ t j s =
      (Polynomial.taylor t (univariateClearedParityCoord I P d_den k ℓ θ s)).coeff j := by
  have htable :
      clearedParityJetTable I P d_den k ℓ J θ t =
        JetTable.ofPolyVPolyZ J ℓ
          (univariateClearedParityProduct I P d_den k ℓ
            (fun x i v => Polynomial.taylor t (θ x i v))) := by
    unfold clearedParityJetTable univariateClearedParityProduct
    rw [map_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [map_prod]
    refine prod_congr rfl fun i _ => ?_
    rw [ofPolyVPolyZ_parityFactorCleared, ofPolyZ_clearedMonomialSumPoly]
  rw [htable, JetTable.ofPolyVPolyZ_apply, ← univariateClearedParityCoord,
    ← taylor_univariateClearedParityCoord]

/-! #### 3.3 Unconditional Hermite–Cramer determinant recovery (Appendix B.3, eq. B.1) -/

/-- **Integer Cramer factorization for `ℤ[X]` (Appendix B.3, eq. B.1, p. 50)**: for any integer
polynomial `p : Polynomial ℤ` with `p.natDegree < Q * J`, replacing column `(0, 0)` of
`Polynomial.hermiteMatrix nodes J` with the order-`J` Taylor jet of `p` at `nodes` yields a
determinant equal to `(Polynomial.hermiteMatrix nodes J).det * p.eval 0`. -/
theorem hermiteCramerNumerator_intPoly_eq_mul {Q J : ℕ} (nodes : Fin Q → ℤ)
    (hQ : 0 < Q) (hJ : 0 < J) {p : Polynomial ℤ} (hdeg : p.natDegree < Q * J) :
    hermiteCramerNumerator nodes hQ hJ (fun i j => (Polynomial.taylor (nodes i) p).coeff j) =
      (Polynomial.hermiteMatrix nodes J).det * p.eval 0 := by
  have hp : p.degree < ↑(Q * J) :=
    Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hdeg)
  have h := Polynomial.det_hermiteMatrix_mul_coeff (R := ℤ) nodes hp (⟨0, hQ⟩, ⟨0, hJ⟩)
  have hmap : (Polynomial.hermiteMatrix nodes J).map (Int.cast : ℤ → ℤ) =
      Polynomial.hermiteMatrix nodes J := by
    ext r c
    simp only [Matrix.map_apply, Int.cast_id]
  have h0 : (finProdFinEquiv (⟨0, hQ⟩, ⟨0, hJ⟩) : ℕ) = 0 := rfl
  rw [hmap, h0, Polynomial.coeff_zero_eq_eval_zero, Int.cast_id] at h
  exact h.symm

/-- **Exact integer Cramer quotient for `ℤ[X]`**: at distinct integer nodes `nodes : Fin Q → ℤ`,
dividing `hermiteCramerNumerator` of `p`'s order-`J` Taylor jet by
`(Polynomial.hermiteMatrix nodes J).det` recovers `p.eval 0`. -/
theorem hermiteCramerNumerator_intPoly_ediv_eq {Q J : ℕ} {nodes : Fin Q → ℤ}
    (hnodes : Function.Injective nodes) (hQ : 0 < Q) (hJ : 0 < J) {p : Polynomial ℤ}
    (hdeg : p.natDegree < Q * J) :
    hermiteCramerNumerator nodes hQ hJ (fun i j => (Polynomial.taylor (nodes i) p).coeff j) /
        (Polynomial.hermiteMatrix nodes J).det =
      p.eval 0 := by
  rw [hermiteCramerNumerator_intPoly_eq_mul nodes hQ hJ hdeg]
  exact Int.mul_ediv_cancel_left (p.eval 0) (Polynomial.det_hermiteMatrix_ne_zero hnodes)

/-- **Cramer numerator factorization for `univariateClearedParityCoord` (Appendix B.3, eq. B.1)**:
when `(k * R_deg) * (#I + 2 * (ℓ - 1)) < Q * J`, the Cramer determinant of the order-`J` Taylor jet
of `univariateClearedParityCoord I P d_den k ℓ θ s` (`s < ℓ`) at `nodes` equals
`(Polynomial.hermiteMatrix nodes J).det * (univariateClearedParityCoord I P d_den k ℓ θ s).eval 0`.
-/
theorem hermiteCramerNumerator_univariateClearedParityCoord_eq_mul [Fintype ι] [DecidableEq ι]
    (I : Finset κ) (P : κ → Finset (Finset ι)) (d_den : ℤ) {k ℓ R_deg Q J s : ℕ}
    (nodes : Fin Q → ℤ) (hQ : 0 < Q) (hJ : 0 < J)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (θ x i v).natDegree ≤ R_deg)
    (hQJ : (k * R_deg) * (#I + 2 * (ℓ - 1)) < Q * J) (hs : s < ℓ) :
    hermiteCramerNumerator nodes hQ hJ
        (fun t j =>
          (Polynomial.taylor (nodes t)
            (univariateClearedParityCoord I P d_den k ℓ θ s)).coeff j) =
      (Polynomial.hermiteMatrix nodes J).det *
        (univariateClearedParityCoord I P d_den k ℓ θ s).eval 0 :=
  hermiteCramerNumerator_intPoly_eq_mul nodes hQ hJ
    ((natDegree_univariateClearedParityCoord_le I P d_den k ℓ θ hk hθ hs).trans_lt hQJ)

/-- **Cramer numerator factorization for `univariateClearedParityTruncatedSum` (Appendix B.3,
eq. B.1)**: under the same degree bound, the Cramer determinant of the order-`J` Taylor jet of
`univariateClearedParityTruncatedSum I P d_den k ℓ θ` at `nodes` equals
`(Polynomial.hermiteMatrix nodes J).det *
  (univariateClearedParityTruncatedSum I P d_den k ℓ θ).eval 0`. -/
theorem hermiteCramerNumerator_univariateClearedParityTruncatedSum_eq_mul
    [Fintype ι] [DecidableEq ι] (I : Finset κ) (P : κ → Finset (Finset ι)) (d_den : ℤ)
    {k ℓ R_deg Q J : ℕ} (nodes : Fin Q → ℤ) (hQ : 0 < Q) (hJ : 0 < J)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (θ x i v).natDegree ≤ R_deg)
    (hQJ : (k * R_deg) * (#I + 2 * (ℓ - 1)) < Q * J) :
    hermiteCramerNumerator nodes hQ hJ
        (fun t j =>
          (Polynomial.taylor (nodes t)
            (univariateClearedParityTruncatedSum I P d_den k ℓ θ)).coeff j) =
      (Polynomial.hermiteMatrix nodes J).det *
        (univariateClearedParityTruncatedSum I P d_den k ℓ θ).eval 0 :=
  hermiteCramerNumerator_intPoly_eq_mul nodes hQ hJ
    ((natDegree_univariateClearedParityTruncatedSum_le I P d_den k ℓ θ hk hθ).trans_lt hQJ)

/-- **Unconditional Hermite–Cramer coordinate recovery of `commonZeroCount` (Appendix B.3,
eq. B.1, p. 50)**: at distinct integer nodes `nodes : Fin Q → ℤ` with `(k * R_deg) * (#I + 2 *
(ℓ - 1)) < Q * J`, `d_den ≠ 0`, and `Fintype.card ι < ℓ`, summing the exact integer Cramer
quotients over `s ∈ range ℓ` and reducing modulo `2 ^ ℓ` recovers `commonZeroCount I P` without
auxiliary `D_H` or `hcramer` hypotheses. -/
theorem emod_sum_hermiteCramerNumerator_ediv_eq_commonZeroCount [Fintype ι] [DecidableEq ι]
    (I : Finset κ) (P : κ → Finset (Finset ι)) {d_den : ℤ} (hd : d_den ≠ 0)
    {k ℓ R_deg Q J : ℕ} {nodes : Fin Q → ℤ} (hnodes : Function.Injective nodes)
    (hQ : 0 < Q) (hJ : 0 < J) (hℓ : Fintype.card ι < ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hdeg : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (θ x i v).natDegree ≤ R_deg)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M,
      (θ x i v).eval 0 = d_den * bitVal ℤ (x v))
    (hQJ : (k * R_deg) * (#I + 2 * (ℓ - 1)) < Q * J) :
    (∑ s ∈ range ℓ,
      hermiteCramerNumerator nodes hQ hJ
        (fun t j =>
          (Polynomial.taylor (nodes t)
            (univariateClearedParityCoord I P d_den k ℓ θ s)).coeff j) /
        (clearedProductDenom d_den k ℓ #I * (Polynomial.hermiteMatrix nodes J).det)) %
          ((2 : ℤ) ^ ℓ) =
      commonZeroCount I P :=
  emod_sum_cramer_ediv_eq_commonZeroCount I P hd (Polynomial.det_hermiteMatrix_ne_zero hnodes) hℓ
    θ _ hk hθ fun _ hs =>
      hermiteCramerNumerator_univariateClearedParityCoord_eq_mul I P d_den nodes hQ hJ θ hk hdeg
        hQJ (mem_range.mp hs)

/-- **Unconditional Hermite–Cramer truncated-sum recovery of `commonZeroCount` (Appendix B.3,
eq. B.1, p. 50)**: under the same hypotheses, dividing the single Cramer determinant of
`univariateClearedParityTruncatedSum I P d_den k ℓ θ` by
`clearedProductDenom d_den k ℓ #I * (Polynomial.hermiteMatrix nodes J).det` and reducing modulo
`2 ^ ℓ` recovers `commonZeroCount I P`. -/
theorem emod_hermiteCramerNumerator_truncatedSum_ediv_eq_commonZeroCount
    [Fintype ι] [DecidableEq ι] (I : Finset κ) (P : κ → Finset (Finset ι)) {d_den : ℤ}
    (hd : d_den ≠ 0) {k ℓ R_deg Q J : ℕ} {nodes : Fin Q → ℤ} (hnodes : Function.Injective nodes)
    (hQ : 0 < Q) (hJ : 0 < J) (hℓ : Fintype.card ι < ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hdeg : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (θ x i v).natDegree ≤ R_deg)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M,
      (θ x i v).eval 0 = d_den * bitVal ℤ (x v))
    (hQJ : (k * R_deg) * (#I + 2 * (ℓ - 1)) < Q * J) :
    (hermiteCramerNumerator nodes hQ hJ
        (fun t j =>
          (Polynomial.taylor (nodes t)
            (univariateClearedParityTruncatedSum I P d_den k ℓ θ)).coeff j) /
      (clearedProductDenom d_den k ℓ #I * (Polynomial.hermiteMatrix nodes J).det)) %
        ((2 : ℤ) ^ ℓ) =
      commonZeroCount I P := by
  have hquot :
      hermiteCramerNumerator nodes hQ hJ
          (fun t j =>
            (Polynomial.taylor (nodes t)
              (univariateClearedParityTruncatedSum I P d_den k ℓ θ)).coeff j) /
        (clearedProductDenom d_den k ℓ #I * (Polynomial.hermiteMatrix nodes J).det) =
      (univariateClearedParityTruncatedSum I P d_den k ℓ θ).eval 0 /
        clearedProductDenom d_den k ℓ #I := by
    rw [hermiteCramerNumerator_univariateClearedParityTruncatedSum_eq_mul I P d_den nodes hQ hJ θ
      hk hdeg hQJ]
    have hℓ1 : 1 ≤ ℓ := by omega
    rw [eval_zero_univariateClearedParityTruncatedSum I P d_den hℓ1 θ hk hθ]
    have hmul :
        (Polynomial.hermiteMatrix nodes J).det *
            (clearedProductDenom d_den k ℓ #I *
              ∑ x : ι → Bool,
                (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x)).sumCoeffsBelow ℓ) =
          (clearedProductDenom d_den k ℓ #I * (Polynomial.hermiteMatrix nodes J).det) *
            ∑ x : ι → Bool,
              (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x)).sumCoeffsBelow ℓ := by
      ring
    rw [hmul,
      Int.mul_ediv_cancel_left _
        (mul_ne_zero (clearedProductDenom_ne_zero hd k ℓ #I)
          (Polynomial.det_hermiteMatrix_ne_zero hnodes)),
      Int.mul_ediv_cancel_left _ (clearedProductDenom_ne_zero hd k ℓ #I)]
  rw [hquot]
  exact emod_ediv_eval_zero_univariateClearedParityTruncatedSum_eq_commonZeroCount I P hd hℓ θ hk hθ

/-! #### 3.4 Canonical jet order and concrete `ReplacementDesign` Hermite–Cramer recovery -/

/-- Canonical confluent Taylor jet order
`J = ⌊(k * (R - 1)) * (m_eq + 2 * (ℓ - 1)) / Q⌋ + 1` for a degree-`≤ k` sparse parity system of
`m_eq` equations at precision `ℓ` under a Section 4 `ReplacementDesign` with degree bound `R - 1`
and `Q` evaluation nodes ([OpenAI2026ETH], equations (3.5) and (5.5), pp. 24, 37). -/
def sparseParityJetOrder (k R Q m_eq ℓ : ℕ) : ℕ :=
  Cslib.ReplacementCounting.jetOrder ((k * (R - 1)) * (m_eq + 2 * (ℓ - 1))) Q

/-- `sparseParityJetOrder` is always positive. -/
theorem sparseParityJetOrder_pos (k R Q m_eq ℓ : ℕ) :
    0 < sparseParityJetOrder k R Q m_eq ℓ :=
  Cslib.ReplacementCounting.jetOrder_pos _ _

/-- When `0 < Q`, `Q * sparseParityJetOrder k R Q m_eq ℓ` strictly exceeds the equation (5.5)
degree bound `(k * (R - 1)) * (m_eq + 2 * (ℓ - 1))`. -/
theorem lt_mul_sparseParityJetOrder (k R m_eq ℓ : ℕ) {Q : ℕ} (hQ : 0 < Q) :
    (k * (R - 1)) * (m_eq + 2 * (ℓ - 1)) < Q * sparseParityJetOrder k R Q m_eq ℓ :=
  Cslib.ReplacementCounting.lt_mul_jetOrder _ hQ

/-- **Concrete `ReplacementDesign` Hermite–Cramer coordinate recovery of `commonZeroCount`
(§5.4 & Appendix B.3, eq. B.1)**: for any `D : ReplacementDesign scope Q r A₀ R τ` with `0 < Q`,
`n < ℓ`, `∀ i ∈ I, ∀ M ∈ P i, #M ≤ k`, and `(k * (R - 1)) * (#I + 2 * (ℓ - 1)) < Q * J` (in
particular for `J = sparseParityJetOrder k R Q #I ℓ`), summing the concrete `hermiteCramerNumerator`
quotients at `nodeInt` over `s ∈ range ℓ` and reducing modulo `2 ^ ℓ` recovers `commonZeroCount I P`
(discharging `D_H ≠ 0` and `hcramer` of `emod_sum_cramer_ediv_design_eq_commonZeroCount`
unconditionally). -/
theorem emod_sum_hermiteCramerNumerator_design_eq_commonZeroCount
    {n Q r A₀ R : ℕ} {τ : ℚ} {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) {k ℓ J : ℕ}
    (hQ : 0 < Q) (hJ : 0 < J) (hℓ : n < ℓ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hQJ : (k * (R - 1)) * (#I + 2 * (ℓ - 1)) < Q * J) :
    (∑ s ∈ range ℓ,
      hermiteCramerNumerator (nodeInt (Q := Q)) hQ hJ
        (fun t j =>
          (Polynomial.taylor (nodeInt t)
            (univariateClearedParityCoord I P (commonDenom Q R : ℤ) k ℓ
              (designReplacementScaledIntMap D emb) s)).coeff j) /
        (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I *
          (Polynomial.hermiteMatrix (nodeInt (Q := Q)) J).det)) % ((2 : ℤ) ^ ℓ) =
      commonZeroCount I P :=
  emod_sum_hermiteCramerNumerator_ediv_eq_commonZeroCount I P (commonDenom_intCast_ne_zero Q R)
    (nodeInt_injective Q) hQ hJ (by simpa only [Fintype.card_fin] using hℓ)
    (designReplacementScaledIntMap D emb) hk
    (fun x i _ _ _ v _ => natDegree_designReplacementScaledIntMap_le D emb x i v)
    (fun x i _ _ _ v _ => eval_zero_designReplacementScaledIntMap D emb x i v) hQJ

/-- **Concrete `ReplacementDesign` Hermite–Cramer truncated-sum recovery of `commonZeroCount`
(§5.4 & Appendix B.3, eq. B.1)**: under the same hypotheses, dividing the single Cramer determinant
of `univariateClearedParityTruncatedSum` at `nodeInt` by
`clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I * (Polynomial.hermiteMatrix nodeInt J).det` and
reducing modulo `2 ^ ℓ` recovers `commonZeroCount I P`. -/
theorem emod_hermiteCramerNumerator_truncatedSum_design_eq_commonZeroCount
    {n Q r A₀ R : ℕ} {τ : ℚ} {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) {k ℓ J : ℕ}
    (hQ : 0 < Q) (hJ : 0 < J) (hℓ : n < ℓ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hQJ : (k * (R - 1)) * (#I + 2 * (ℓ - 1)) < Q * J) :
    (hermiteCramerNumerator (nodeInt (Q := Q)) hQ hJ
        (fun t j =>
          (Polynomial.taylor (nodeInt t)
            (univariateClearedParityTruncatedSum I P (commonDenom Q R : ℤ) k ℓ
              (designReplacementScaledIntMap D emb))).coeff j) /
      (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I *
        (Polynomial.hermiteMatrix (nodeInt (Q := Q)) J).det)) % ((2 : ℤ) ^ ℓ) =
      commonZeroCount I P :=
  emod_hermiteCramerNumerator_truncatedSum_ediv_eq_commonZeroCount I P
    (commonDenom_intCast_ne_zero Q R) (nodeInt_injective Q) hQ hJ
    (by simpa only [Fintype.card_fin] using hℓ) (designReplacementScaledIntMap D emb) hk
    (fun x i _ _ _ v _ => natDegree_designReplacementScaledIntMap_le D emb x i v)
    (fun x i _ _ _ v _ => eval_zero_designReplacementScaledIntMap D emb x i v) hQJ

/-- **§5.5 & Appendix B.3 branch-summed concrete Hermite–Cramer recovery of `commonZeroCount` at
shared precision $\ell = n + 1$ and canonical jet order `sparseParityJetOrder`**: given a
heavy-variable subset `S : Finset (Fin n)`, a free-variable relabeling `e : ↥(univ \ S) ≃ Fin n'`,
and a per-branch `ReplacementDesign` family `D b` (`0 < Q`), summing the branch modular residues of
the concrete `hermiteCramerNumerator` quotients at `nodeInt` and jet order
`J = sparseParityJetOrder k R Q #I (branchPrecision n)` across `b ∈ branchAssignments S` recovers
`commonZeroCount I P`. -/
theorem commonZeroCount_eq_sum_branch_hermiteCramerNumerator_design
    {n n' Q r A₀ R : ℕ} {τ : ℚ} {F : Type*} [Fintype F]
    (S : Finset (Fin n)) (e : ↥(univ \ S) ≃ Fin n')
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) {k : ℕ}
    (scope : (Fin n → Bool) → F → Finset (Fin n'))
    (D : (b : Fin n → Bool) → ReplacementDesign (scope b) Q r A₀ R τ)
    (emb : (Fin n → Bool) → κ → F)
    (hQ : 0 < Q) (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k) :
    let ℓ := branchPrecision n
    let J := sparseParityJetOrder k R Q #I ℓ
    (commonZeroCount I P : ℤ) =
      ∑ b ∈ branchAssignments S,
        (hermiteCramerNumerator (nodeInt (Q := Q)) hQ (sparseParityJetOrder_pos k R Q #I ℓ)
          (fun t j =>
            (Polynomial.taylor (nodeInt t)
              (univariateClearedParityTruncatedSum I
                (fun i => relabelRestrictedMonomials S e b (P i))
                (commonDenom Q R : ℤ) k ℓ
                (designReplacementScaledIntMap (D b) (emb b)))).coeff j) /
          (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I *
            (Polynomial.hermiteMatrix (nodeInt (Q := Q)) J).det)) % ((2 : ℤ) ^ ℓ) := by
  intro ℓ J
  rw [commonZeroCount_eq_sum_branch_emod_ediv_design S e I P scope D emb hk]
  refine sum_congr rfl fun b _ => ?_
  have hlt : n' < ℓ := by
    have hle : n' ≤ n := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_congr e).symm.trans_le (Fintype.card_subtype_le _)
    change n' < n + 1
    omega
  have hk_branch : ∀ i ∈ I, ∀ M ∈ relabelRestrictedMonomials S e b (P i), #M ≤ k :=
    fun i hi M hM => card_mem_relabelRestrictedMonomials_le (hk i hi) M hM
  rw [emod_hermiteCramerNumerator_truncatedSum_design_eq_commonZeroCount (D b) (emb b) I
    (fun i => relabelRestrictedMonomials S e b (P i)) hQ (sparseParityJetOrder_pos k R Q #I ℓ)
    hlt hk_branch (lt_mul_sparseParityJetOrder k R #I ℓ hQ)]
  exact emod_ediv_eval_zero_clearedParityTruncatedSum_design_eq_commonZeroCount (D b) (emb b) I
    (fun i => relabelRestrictedMonomials S e b (P i)) hlt hk_branch

end Cslib.BitString
