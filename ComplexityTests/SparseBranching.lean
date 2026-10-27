/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseBranching
public import ComplexityTests.SparseEquations

/-!
# Tests for univariate parity-product specialization and heavy-variable branch reduction

Concrete non-vacuity checks and edge-case controls for
`Complexity.Foundations.BooleanAnalysis.SparseBranching`.
-/

@[expose] public noncomputable section

namespace Cslib.BitString

open Finset

/-- Linear univariate replacement polynomial `bitVal ℤ (x v) + T` of degree `1`, which restores
`bitVal ℤ (x v)` at `T = 0`. -/
def testLinearReplacement (x : Fin 2 → Bool) (_i : Fin 2) (v : Fin 2) : Polynomial ℤ :=
  Polynomial.C (bitVal ℤ (x v)) + Polynomial.X

/-- At `T = 0`, `testLinearReplacement x i v` restores `bitVal ℤ (x v)`. -/
theorem eval_zero_testLinearReplacement (x : Fin 2 → Bool) (i v : Fin 2) :
    (testLinearReplacement x i v).eval 0 = bitVal ℤ (x v) := by
  simp only [testLinearReplacement, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    add_zero]

/-- Equation (5.5a) univariate `natDegree` bound (`k = 2`, `R_deg = 3`, `#I = 2`, `ℓ = 2`):
both `[V ^ 1] H(T)` and `S_2(H(T))` have `natDegree ≤ (2 * 3) * (2 + 2 * 1) = 24`. -/
example (q : (Fin 2 → Bool) → Fin 2 → Fin 2 → Polynomial ℤ)
    (hq : ∀ x : Fin 2 → Bool, ∀ i ∈ (univ : Finset (Fin 2)), ∀ M ∈ testSys i, ∀ v ∈ M,
      (q x i v).natDegree ≤ 3) :
    (univariateParityCoord (univ : Finset (Fin 2)) testSys 2 q 1).natDegree ≤ 24 ∧
      (univariateParityTruncatedSum (univ : Finset (Fin 2)) testSys 2 q).natDegree ≤ 24 := by
  have hk : ∀ i ∈ (univ : Finset (Fin 2)), ∀ M ∈ testSys i, #M ≤ 2 := by
    intro i _ M _
    exact (card_le_univ M).trans (by decide)
  exact ⟨(natDegree_univariateParityCoord_le univ testSys 2 q hk hq (by decide)).trans (by decide),
    (natDegree_univariateParityTruncatedSum_le univ testSys 2 q hk hq).trans (by decide)⟩

/-- Equation (5.5b) exact recovery at `T = 0` on `testSys` with `testLinearReplacement` and
precision `ℓ = 3 > Fintype.card (Fin 2)`: reducing `S_3(H(0))` modulo `2 ^ 3 = 8` recovers
`commonZeroCount univ testSys = 1`. -/
example :
    ((univariateParityTruncatedSum (univ : Finset (Fin 2)) testSys 3
      testLinearReplacement).eval 0) % ((2 : ℤ) ^ 3) =
      commonZeroCount (univ : Finset (Fin 2)) testSys :=
  emod_eval_zero_univariateParityTruncatedSum_eq_commonZeroCount univ testSys (by decide)
    testLinearReplacement (fun x i _ _ _ v _ => eval_zero_testLinearReplacement x i v)

/-- Theorem 2.2 additive branch decomposition on the relabeled free-variable cube `Fin n' → Bool`
when branching on `S = {0}` (`n' = #(univ \ {0})`). -/
example :
    commonZeroCount (univ : Finset (Fin 2)) testSys =
      ∑ b ∈ branchAssignments ({0} : Finset (Fin 2)),
        commonZeroCount (univ : Finset (Fin 2))
          (fun i => relabelRestrictedMonomials ({0} : Finset (Fin 2))
            (equivFin (univ \ ({0} : Finset (Fin 2)))) b (testSys i)) :=
  commonZeroCount_eq_sum_relabelRestrictedMonomials {0}
    (equivFin (univ \ ({0} : Finset (Fin 2)))) univ testSys

/-- Post-branching free-variable incidence bound `≤ b₀` on the relabeled variable type `Fin n'`
for `testSys` with `b₀ = 1`. -/
example (b : Fin 2 → Bool)
    (w : Fin #(univ \ heavyVars univ univ (fun i => equationScope (testSys i)) 1)) :
    varIncidence (univ : Finset (Fin 2))
      (fun i => equationScope
        (relabelRestrictedMonomials
          (heavyVars univ univ (fun i => equationScope (testSys i)) 1)
          (equivFin (univ \ heavyVars univ univ (fun i => equationScope (testSys i)) 1))
          b (testSys i))) w ≤ 1 :=
  varIncidence_relabelRestrictedMonomials_heavyVars_le univ univ testSys 1
    (subset_univ _)
    (equivFin (univ \ heavyVars univ univ (fun i => equationScope (testSys i)) 1)) b w

/-- Neutral singleton variable-coverage scopes guarantee `1 ≤ varIncidence` for every variable and
`Fintype.card (Fin 2) ≤ totalIncidence`. -/
example (v : Fin 2) :
    1 ≤ varIncidence (withNeutralFactors (univ : Finset (Fin 2)))
      (withNeutralScope (fun i => equationScope (testSys i))) v ∧
    Fintype.card (Fin 2) ≤
      totalIncidence (withNeutralFactors (univ : Finset (Fin 2)))
        (withNeutralScope (fun i => equationScope (testSys i))) :=
  ⟨one_le_varIncidence_withNeutralFactors univ (fun i => equationScope (testSys i)) v,
    card_le_totalIncidence_withNeutralFactors univ (fun i => equationScope (testSys i))⟩

/-- Heavy-variable threshold ceiling `heavyThreshold M n s` satisfies `M * s ≤ b₀ * n` and yields
at least `n / 2` free variables when `s ≥ 2`. -/
example :
    4 * 2 ≤ heavyThreshold 4 20 2 * 20 :=
  mul_le_heavyThreshold_mul (by decide)

end Cslib.BitString
