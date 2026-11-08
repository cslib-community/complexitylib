/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic
public import CslibFrontier.Computability.Circuit.SourceComplexity
public import CslibFrontier.Foundations.Data.MvPolynomial.HessianRank
import CslibFrontier.Computability.Circuit.Arithmetic.Hessian

/-!
# Hessian bounds for minimum multiplication cost

Minimum residual Hessian rank is at most twice the minimum multiplication cost from arbitrary
supplied formal polynomials. No construction of the supplied polynomials is charged. The common
source domain is `Unit` and the carrier consists of formal polynomials: correctness is polynomial
equality, not equality of polynomial functions. All field characteristics are allowed.

The bounds remain valid when no circuit computes the target, since its complexity is then `⊤`.
When raw variables are supplied alongside helpers, only the helper Hessians need to be subtracted.

## Main results

* `Cslib.Circuits.hessianResidualRank_le_two_mul_ecomplexityFrom`: arbitrary supplied polynomials.
* `Cslib.Circuits.hessianResidualRank_le_two_mul_ecomplexityFrom_with_helpers`:
  raw variables and helpers.
* `Cslib.Circuits.le_ecomplexityFrom_of_hessian_rank`: a uniform residual-rank lower bound.

## References

* Ported from LowerBound/Fusion/Arithmetic/Interaction/Hessian/Relative.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits

open MvPolynomial

variable {C K ι : Type*} [Field K] [Fintype ι] {n k : ℕ}

/-- The least residual Hessian rank is at most twice the least multiplication cost. -/
theorem hessianResidualRank_le_two_mul_ecomplexityFrom (constant : C → K) (point : ι → K)
    (target : MvPolynomial ι K) (sources : Fin n → MvPolynomial ι K) :
    hessianResidualRank point target sources ≤ 2 *
      ecomplexityFrom (arithInterpretationWith C (MvPolynomial.C ∘ constant)) ArithOp.mulCost
        (fun (_ : Unit) (_ : Fin 1) => target) (fun _ => sources) := by
  rw [ecomplexityFrom, ENat.mul_iInf_of_ne (by decide : (2 : ℕ∞) ≠ 0)]
  refine le_iInf fun c => ?_
  obtain ⟨coefficients, h⟩ := c.1.exists_hessian_residual constant point sources 0 target
    (congrFun (c.2 ()) 0)
  exact (hessianResidualRank_le point target sources coefficients).trans (by exact_mod_cast h)

/-- Supplying raw variables with helpers requires subtracting only the helper Hessians. -/
theorem hessianResidualRank_le_two_mul_ecomplexityFrom_with_helpers (constant : C → K)
    (point : Fin n → K) (target : MvPolynomial (Fin n) K)
    (helpers : Fin k → MvPolynomial (Fin n) K) :
    hessianResidualRank point target helpers ≤ 2 *
      ecomplexityFrom (arithInterpretationWith C (MvPolynomial.C ∘ constant)) ArithOp.mulCost
        (fun (_ : Unit) (_ : Fin 1) => target) (fun _ => Fin.append X helpers) := by
  rw [ecomplexityFrom, ENat.mul_iInf_of_ne (by decide : (2 : ℕ∞) ≠ 0)]
  refine le_iInf fun c => ?_
  obtain ⟨coefficients, h⟩ := c.1.exists_helper_hessian_residual constant point helpers 0 target
    (congrFun (c.2 ()) 0)
  exact (hessianResidualRank_le point target helpers coefficients).trans (by exact_mod_cast h)

/-- A lower bound on every residual Hessian bounds minimum multiplication cost. -/
theorem le_ecomplexityFrom_of_hessian_rank (constant : C → K) (point : ι → K)
    (target : MvPolynomial ι K) (sources : Fin n → MvPolynomial ι K) (lower : ℕ)
    (hlower : ∀ coefficients : Fin n → K,
      2 * lower ≤ (hessian point target - ∑ i, coefficients i • hessian point (sources i)).rank) :
    (lower : ℕ∞) ≤
      ecomplexityFrom (arithInterpretationWith C (MvPolynomial.C ∘ constant)) ArithOp.mulCost
        (fun (_ : Unit) (_ : Fin 1) => target) (fun _ => sources) := by
  apply le_ecomplexityFrom_iff.mpr
  intro c hc
  obtain ⟨coefficients, h⟩ := c.exists_hessian_residual constant point sources 0 target
    (congrFun (hc ()) 0)
  have := (hlower coefficients).trans h
  exact_mod_cast (by lia : lower ≤ c.program.cost ArithOp.mulCost)

end Cslib.Circuits
