/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseEquations

/-!
# Tests for sparse `𝔽₂` polynomial equations, common-zero recovery, and heavy-variable branching

Concrete non-vacuity checks and edge-case controls for
`Complexity.Foundations.BooleanAnalysis.SparseEquations`.
-/

@[expose] public section

namespace Cslib.BitString

open Finset MvPolynomial

/-- Equation `x₀ x₁ + 1 = 0` on `Fin 2 → Bool`: only `(true, true)` is a root over `𝔽₂`. -/
def testEq0 : Finset (Finset (Fin 2)) :=
  {{0, 1}, ∅}

/-- Equation `x₀ + x₁ = 0` on `Fin 2 → Bool`: `(false, false)` and `(true, true)` are roots. -/
def testEq1 : Finset (Finset (Fin 2)) :=
  {{0}, {1}}

/-- Concrete 2-equation system `{testEq0, testEq1}` on `Fin 2 → Bool` with unique common zero
`(true, true)`. -/
def testSys : Fin 2 → Finset (Finset (Fin 2))
  | 0 => testEq0
  | 1 => testEq1

/-- At `(true, true)`, `testEq0` has `2` satisfied monomials (`{0, 1}` and `∅`), so its integer
evaluation is `2` (even) and its `ZMod 2` evaluation is `0`. -/
example : monomialSum ℤ testEq0 (fun _ => true) = 2 := by
  decide

example : monomialSum (ZMod 2) testEq0 (fun _ => true) = 0 := by
  decide

/-- `testSys` has a unique common zero `(true, true)` on `Fin 2 → Bool`. -/
example : commonZeroCount (univ : Finset (Fin 2)) testSys = 1 := by
  decide

/-- Both variables `0` and `1` appear in both equations of `testSys`, so both are heavy at
threshold `b₀ = 1`. -/
example : heavyVars univ univ (fun i => equationScope (testSys i)) 1 = {0, 1} := by
  decide

/-- Equation (5.1) on `testSys`: the cube sum of products of evenness indicators equals
`commonZeroCount univ testSys`. -/
example :
    (∑ x : Fin 2 → Bool,
      ∏ i ∈ (univ : Finset (Fin 2)),
        if Even (monomialSum ℤ (testSys i) x) then (1 : ℤ) else 0) =
      commonZeroCount (univ : Finset (Fin 2)) testSys :=
  sum_prod_even_monomialSum_eq_commonZeroCount univ testSys

/-- Equation (5.4) exact recovery on `testSys` at precision `ℓ = 3 > Fintype.card (Fin 2)`:
reducing the cube sum of truncated parity-factor products modulo `2 ^ 3 = 8` recovers
`commonZeroCount univ testSys` on the nose. -/
example :
    (∑ x : Fin 2 → Bool,
      Polynomial.sumCoeffsBelow 3
        (∏ i ∈ (univ : Finset (Fin 2)),
          Polynomial.parityFactor 3 (monomialSum ℤ (testSys i) x))) % ((2 : ℤ) ^ 3) =
      commonZeroCount (univ : Finset (Fin 2)) testSys :=
  emod_sum_sumCoeffsBelow_prod_parityFactor_eq_commonZeroCount univ testSys (by decide)

/-- Edge cases: empty equation set has `2 ^ 2 = 4` common zeros, while a system containing `{∅}`
(`1 = 0`) has `0` common zeros. -/
example : commonZeroCount (∅ : Finset (Fin 2)) testSys = 4 :=
  commonZeroCount_empty testSys

example :
    commonZeroCount ({0} : Finset (Fin 1)) (fun _ => ({∅} : Finset (Finset (Fin 2)))) = 0 :=
  commonZeroCount_eq_zero_of_singleton_empty (mem_singleton_self 0) rfl

/-- Equation (5.5) total-degree bound under degree-`d₀` variable replacement (`k = 2`, `d₀ = 3`,
`#I = 2`, `ℓ = 2`): the truncated product has total degree at most `(2 * 3) * (2 + 2 * 1) = 24`. -/
example (q : Fin 2 → Fin 2 → MvPolynomial (Fin 3) ℤ)
    (hq : ∀ i ∈ (univ : Finset (Fin 2)), ∀ M ∈ testSys i, ∀ v ∈ M, (q i v).totalDegree ≤ 3) :
    (Polynomial.sumCoeffsBelow 2
      (∏ i ∈ (univ : Finset (Fin 2)),
        Polynomial.parityFactor 2
          ((monomialSumPoly ℤ (testSys i)).eval₂ MvPolynomial.C (q i)))).totalDegree ≤ 24 := by
  have hk : ∀ i ∈ (univ : Finset (Fin 2)), ∀ M ∈ testSys i, #M ≤ 2 := by
    intro i _ M _
    exact (card_le_univ M).trans (by decide)
  have h := totalDegree_sumCoeffsBelow_prod_parityFactor_eval₂_le
    (I := (univ : Finset (Fin 2))) (P := testSys) 2 (k := 2) (d₀ := 3)
    MvPolynomial.C q hk hq
  exact h.trans (by decide)

/-- Modulo-`2` cancellation under `restrictMonomials`: specializing `S = {0}` to `b 0 = true` in
`{{0, 1}, {1}}` (`x₀ x₁ + x₁`) maps both monomials to `{1}`, so their coefficients cancel modulo
`2` and `restrictMonomials {0} (fun _ => true) {{0, 1}, {1}} = ∅`. -/
example :
    restrictMonomials ({0} : Finset (Fin 2)) (fun _ => true)
      ({{0, 1}, {1}} : Finset (Finset (Fin 2))) = ∅ := by
  decide

/-- Under `b 0 = false`, only `{1}` survives, so `restrictMonomials` retains `{{1}}`. -/
example :
    restrictMonomials ({0} : Finset (Fin 2)) (fun _ => false)
      ({{0, 1}, {1}} : Finset (Finset (Fin 2))) = {{1}} := by
  decide

/-- Heavy-variable bound and post-branching incidence bound for `testSys` with threshold `b₀ = 1`:
both variables have incidence `2 > 1`, and after branching on `heavyVars`, every variable has
incidence `0 ≤ 1` in the reduced scopes. -/
example (b : Fin 2 → Bool) (v : Fin 2) :
    varIncidence (univ : Finset (Fin 2))
      (fun i => equationScope
        (restrictMonomials
          (heavyVars univ univ (fun i => equationScope (testSys i)) 1) b (testSys i))) v ≤ 1 :=
  varIncidence_equationScope_restrictMonomials_heavyVars_le univ univ testSys 1
    (fun _ _ => subset_univ _) b v

/-- Additive branch decomposition of `commonZeroCount` when branching on `S = {0}`. -/
example :
    commonZeroCount (univ : Finset (Fin 2)) testSys =
      ∑ b ∈ branchAssignments ({0} : Finset (Fin 2)),
        #{y ∈ subproblemAssignments ({0} : Finset (Fin 2)) |
          IsCommonZero univ (fun i => restrictMonomials ({0} : Finset (Fin 2)) b (testSys i)) y} :=
  commonZeroCount_eq_sum_branches {0} univ testSys

/-- Section 5.4 & Appendix B.2: cleared-denominator homogenization of the truncated parity-factor
product (`ℓ = 3`, `2 * ℓ - 1 = 5`, `#I = 2`, so `Ω = (Δ ^ 5) ^ 2`). -/
example (Δ : ℤ) (x : Fin 2 → Bool) :
    (∏ i ∈ (univ : Finset (Fin 2)),
      parityFactorCleared 3 Δ (Δ * monomialSum ℤ (testSys i) x)).sumCoeffsBelow 3 =
      (Δ ^ (2 * 3 - 1)) ^ #(univ : Finset (Fin 2)) *
        (∏ i ∈ (univ : Finset (Fin 2)),
          Polynomial.parityFactor 3 (monomialSum ℤ (testSys i) x)).sumCoeffsBelow 3 :=
  sumCoeffsBelow_prod_parityFactorCleared_mul univ (by decide) Δ
    (fun i => monomialSum ℤ (testSys i) x) 3

/-- Appendix B.2 `ℓ₁`-norm bound for a cleared degree-`2` monomial sum `testEq0` (`#testEq0 = 2`)
when `d_den` and every replacement numerator `θ v` have `coeffNorm1 ≤ 4`:
`coeffNorm1 ≤ 2 * 4 ^ 2 = 32`. -/
example (d_den : ℤ) (θ : Fin 2 → Polynomial ℤ)
    (hd : d_den.natAbs ≤ 4)
    (hθ : ∀ M ∈ testEq0, ∀ v ∈ M, Polynomial.coeffNorm1 (θ v) ≤ 4) :
    Polynomial.coeffNorm1 (clearedMonomialSumPoly d_den 2 θ testEq0) ≤ 32 := by
  have hk : ∀ M ∈ testEq0, #M ≤ 2 := fun M _ => (card_le_univ M).trans (by decide)
  exact (coeffNorm1_clearedMonomialSumPoly_le hd hk hθ).trans (by decide)

/-- Appendix B.2 `ℓ₁`-norm bound for the `V ^ 1`-coefficient of `parityFactorCleared` (`ℓ = 2`,
`B = 10`, `Δ = 3`): `coeffNorm1 ≤ 2 * (4 ^ 1 * 2 ^ 6) * (10 + 3) ^ 3 = 1124864`. -/
example (A_i : Polynomial ℤ) (hA : Polynomial.coeffNorm1 A_i ≤ 10) :
    Polynomial.coeffNorm1 ((parityFactorCleared 2 (Polynomial.C (3 : ℤ)) A_i).coeff 1) ≤
      1124864 :=
  (coeffNorm1_coeff_parityFactorCleared_le_explicit 2 3 hA 1).trans (by decide)

end Cslib.BitString
