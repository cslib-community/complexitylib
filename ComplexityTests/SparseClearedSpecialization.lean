/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseClearedSpecialization
public import ComplexityTests.SparseBranching
public import Mathlib.Data.Rat.Defs

/-!
# Tests for rational-to-cleared-denominator specialization and exact division recovery

Concrete non-vacuity checks and edge-case controls for
`Complexity.Foundations.BooleanAnalysis.SparseClearedSpecialization`.
-/

@[expose] public noncomputable section

namespace Cslib.BitString

open Finset

/-- Cleared-denominator linear replacement numerator `3 * bitVal ℤ (x v) + T` over common
denominator `d_den = 3`, which evaluates to `3 * bitVal ℤ (x v)` at `T = 0`. -/
def testClearedLinearNumerator (x : Fin 2 → Bool) (_i : Fin 2) (v : Fin 2) : Polynomial ℤ :=
  Polynomial.C (3 * bitVal ℤ (x v)) + Polynomial.X

/-- At `T = 0`, `testClearedLinearNumerator x i v` evaluates to `3 * bitVal ℤ (x v)`. -/
theorem eval_zero_testClearedLinearNumerator (x : Fin 2 → Bool) (i v : Fin 2) :
    (testClearedLinearNumerator x i v).eval 0 = 3 * bitVal ℤ (x v) := by
  simp only [testClearedLinearNumerator, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, add_zero]

/-- Equation (5.5a) cleared-denominator `natDegree` bound (`k = 2`, `R_deg = 3`, `#I = 2`, `ℓ = 2`,
`d_den = 3`): both `[V ^ 1] \tilde{H}(T)` and `S_2(\tilde{H}(T))` have `natDegree ≤ 24`. -/
example (θ : (Fin 2 → Bool) → Fin 2 → Fin 2 → Polynomial ℤ)
    (hθ : ∀ x : Fin 2 → Bool, ∀ i ∈ (univ : Finset (Fin 2)), ∀ M ∈ testSys i, ∀ v ∈ M,
      (θ x i v).natDegree ≤ 3) :
    (univariateClearedParityCoord (univ : Finset (Fin 2)) testSys 3 2 2 θ 1).natDegree ≤ 24 ∧
      (univariateClearedParityTruncatedSum (univ : Finset (Fin 2)) testSys 3 2 2 θ).natDegree ≤
        24 := by
  have hk : ∀ i ∈ (univ : Finset (Fin 2)), ∀ M ∈ testSys i, #M ≤ 2 := by
    intro _i _ M _
    exact (card_le_univ M).trans (by decide)
  exact ⟨(natDegree_univariateClearedParityCoord_le univ testSys 3 2 2 θ hk hθ (by decide)).trans
      (by decide),
    (natDegree_univariateClearedParityTruncatedSum_le univ testSys 3 2 2 θ hk hθ).trans
      (by decide)⟩

/-- §5.4 & Appendix B.3 rational homogenization over `ℚ` (`d_den = 3`, `k = 2`, `ℓ = 3`):
mapping `univariateClearedParityCoord` into `ℚ[T]` equals `C (clearedProductDenom 3 2 3 #univ : ℚ)`
times the rational `univariateParityCoord` for `divDenomReplacement ℚ 3`. -/
example (s : ℕ) :
    (univariateClearedParityCoord (univ : Finset (Fin 2)) testSys 3 2 3
      testClearedLinearNumerator s).map (Int.castRingHom ℚ) =
      Polynomial.C (clearedProductDenom 3 2 3 #(univ : Finset (Fin 2)) : ℚ) *
        univariateParityCoord (univ : Finset (Fin 2)) testSys 3
          (divDenomReplacement ℚ 3 testClearedLinearNumerator) s := by
  have hk : ∀ i ∈ (univ : Finset (Fin 2)), ∀ M ∈ testSys i, #M ≤ 2 := by
    intro _i _ M _
    exact (card_le_univ M).trans (by decide)
  exact map_univariateClearedParityCoord_divDenomReplacement univ testSys (by decide) (by decide)
    testClearedLinearNumerator hk s

/-- §5.4 & Appendix B.3 exact integer division and modular recovery at `T = 0` (`d_den = 3`,
`k = 2`, `ℓ = 3 > Fintype.card (Fin 2)`): dividing each cleared coordinate value at `0` by
`clearedProductDenom 3 2 3 2`, summing over `s ∈ range 3`, and reducing modulo `2 ^ 3 = 8`
recovers `commonZeroCount univ testSys = 1`. -/
example :
    (∑ s ∈ range 3,
      (univariateClearedParityCoord (univ : Finset (Fin 2)) testSys 3 2 3
        testClearedLinearNumerator s).eval 0 /
        clearedProductDenom 3 2 3 #(univ : Finset (Fin 2))) % ((2 : ℤ) ^ 3) =
      commonZeroCount (univ : Finset (Fin 2)) testSys := by
  have hk : ∀ i ∈ (univ : Finset (Fin 2)), ∀ M ∈ testSys i, #M ≤ 2 := by
    intro _i _ M _
    exact (card_le_univ M).trans (by decide)
  exact emod_sum_ediv_eval_zero_univariateClearedParityCoord_eq_commonZeroCount univ testSys
    (by decide) (by decide) testClearedLinearNumerator hk
    (fun x i _ _ _ v _ => eval_zero_testClearedLinearNumerator x i v)

/-- Appendix B.3 (eq. B.1) Cramer's rule determinant recovery with `d_den = 3` and `D_H = 5`. -/
example :
    (∑ s ∈ range 3,
      (5 * (univariateClearedParityCoord (univ : Finset (Fin 2)) testSys 3 2 3
        testClearedLinearNumerator s).eval 0) /
        (clearedProductDenom 3 2 3 #(univ : Finset (Fin 2)) * 5)) % ((2 : ℤ) ^ 3) =
      commonZeroCount (univ : Finset (Fin 2)) testSys := by
  have hk : ∀ i ∈ (univ : Finset (Fin 2)), ∀ M ∈ testSys i, #M ≤ 2 := by
    intro _i _ M _
    exact (card_le_univ M).trans (by decide)
  exact emod_sum_cramer_ediv_eq_commonZeroCount univ testSys (by decide) (by decide) (by decide)
    testClearedLinearNumerator
    (fun s =>
      5 * (univariateClearedParityCoord univ testSys 3 2 3 testClearedLinearNumerator s).eval 0)
    hk (fun x i _ _ _ v _ => eval_zero_testClearedLinearNumerator x i v)
    (fun _ _ => rfl)

/-- §5.5 & Appendix B.3 branch-summed exact integer division recovery on `testSys` when branching
on `S = {0}` at shared precision `ℓ = branchPrecision 2 = 3`. -/
example :
    (commonZeroCount (univ : Finset (Fin 2)) testSys : ℤ) =
      ∑ b ∈ branchAssignments ({0} : Finset (Fin 2)),
        ((univariateClearedParityTruncatedSum (univ : Finset (Fin 2))
          (fun i => relabelRestrictedMonomials ({0} : Finset (Fin 2))
            (equivFin (univ \ ({0} : Finset (Fin 2)))) b (testSys i))
          3 2 (branchPrecision (Fintype.card (Fin 2)))
          (fun x _i w => Polynomial.C (3 * bitVal ℤ (x w)) + Polynomial.X)).eval 0 /
            clearedProductDenom 3 2 (branchPrecision (Fintype.card (Fin 2)))
              #(univ : Finset (Fin 2))) %
                ((2 : ℤ) ^ branchPrecision (Fintype.card (Fin 2))) := by
  have hk : ∀ i ∈ (univ : Finset (Fin 2)), ∀ M ∈ testSys i, #M ≤ 2 := by
    intro _i _ M _
    exact (card_le_univ M).trans (by decide)
  refine commonZeroCount_eq_sum_branch_emod_ediv_cleared {0}
    (equivFin (univ \ ({0} : Finset (Fin 2)))) univ testSys (by decide) _ hk ?_
  intro _b _hb x _i _hi _M _hM w _hw
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, add_zero]

/-- Appendix B.2 coordinate `coeffNorm1` bound on `testSys` (`d_den = 3`, `k = 2`, `ℓ = 2`,
`B = 10`, `E_ℓ = 100`, `#I = 2`, `n = 2`). -/
example (θ : (Fin 2 → Bool) → Fin 2 → Fin 2 → Polynomial ℤ)
    (hA : ∀ x : Fin 2 → Bool, ∀ i ∈ (univ : Finset (Fin 2)),
      (clearedMonomialSumPoly 3 2 (θ x i) (testSys i)).coeffNorm1 ≤ 10)
    (hE : ∀ j < 2, (Polynomial.parityBaseDigit 2 j).coeffNorm1 ≤ 100) (s : ℕ) :
    (univariateClearedParityCoord (univ : Finset (Fin 2)) testSys 3 2 2 θ s).coeffNorm1 ≤
      2 ^ Fintype.card (Fin 2) *
        (2 * 100 * (10 + ((3 : ℤ) ^ 2).natAbs) ^ (2 * 2 - 1)) ^ #(univ : Finset (Fin 2)) :=
  coeffNorm1_univariateClearedParityCoord_le univ testSys 3 2 2 θ hA hE s

end Cslib.BitString
