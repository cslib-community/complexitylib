/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseReplacementDesign
import Mathlib.Tactic.NormNum

/-!
# Tests for `Complexity.Foundations.BooleanAnalysis.SparseReplacementDesign`

Concrete checks and nonvacuous witnesses for neutral-singleton augmented equation scopes,
`designRowNormBound`, `exists_replacementDesign_augmentedEquationScope`, and the
`ReplacementDesign` specializations of cleared-denominator zero counting and heavy-variable
branch recovery.
-/

@[expose] public noncomputable section

namespace Cslib.BitString.SparseReplacementDesignTests

open Finset Polynomial
open scoped BigOperators
open Cslib.BalancedSchedules Cslib.LinearAlgebra

/-- Concrete equation family on `Fin 3` with two equations:
- equation `0`: `x₀ + x₀ x₁ = 0` (monomials `{0}`, `{0, 1}`; scope `{0, 1}`),
- equation `1`: `x₁ x₂ + 1 = 0` (monomials `{1, 2}`, `∅`; scope `{1, 2}`).
Its satisfying assignments are `(false, true, true)` and `(true, true, true)` (`2` common zeros). -/
def sampleEqs : Fin 2 → Finset (Finset (Fin 3))
  | ⟨0, _⟩ => {{0}, {0, 1}}
  | ⟨1, _⟩ => {{1, 2}, ∅}

/-- Expected-value control: `sampleEqs` has `commonZeroCount = 2`, while the empty equation set has
`commonZeroCount = 8`. -/
example :
    commonZeroCount univ sampleEqs = 2 ∧
    commonZeroCount (∅ : Finset (Fin 2)) sampleEqs = 8 := by
  decide

/-- Total incidence of `augmentedEquationScope sampleEqs` is `(2 + 2) + 3 = 7 ≥ 3`. -/
example :
    (∑ f : Fin 2 ⊕ Fin 3, #(augmentedEquationScope sampleEqs f)) = 7 ∧
      3 ≤ ∑ f : Fin 2 ⊕ Fin 3, #(augmentedEquationScope sampleEqs f) := by
  refine ⟨?_, le_sum_card_augmentedEquationScope sampleEqs⟩
  rw [sum_card_augmentedEquationScope]
  decide

/-- Variable `1 : Fin 3` belongs to both equation scopes plus its neutral singleton scope
(`2 + 1 = 3` scopes total), whereas variable `0 : Fin 3` belongs to `1 + 1 = 2` scopes. -/
example :
    #{f : Fin 2 ⊕ Fin 3 | (1 : Fin 3) ∈ augmentedEquationScope sampleEqs f} = 3 ∧
      #{f : Fin 2 ⊕ Fin 3 | (0 : Fin 3) ∈ augmentedEquationScope sampleEqs f} = 2 := by
  rw [card_filter_mem_augmentedEquationScope, card_filter_mem_augmentedEquationScope]
  decide

/-- Explicit value of `designRowNormBound 3 2`:
`commonDenom 3 2 = 1! * 3! = 6` and `1 + (1 + 2 ^ 3) * 2 * (4 * 3) ^ 1 = 1 + 9 * 2 * 12 = 217`,
so `designRowNormBound 3 2 = 6 * 217 = 1302`. -/
example :
    commonDenom 3 2 = 6 ∧
      designRowNormBound 3 2 = 1302 ∧
      commonDenom 3 2 ≤ designRowNormBound 3 2 ∧
      0 < designRowNormBound 3 2 := by
  refine ⟨by decide, by decide, commonDenom_le_designRowNormBound 3 2, designRowNormBound_pos 3 2⟩

/-- Canonical `Q = 1, r = 1, A₀ = 0, R = 1, τ = 0` replacement design for any scope family on
`Fin n` (`1 ≤ n`), used to exercise concrete branch-recovery and degree/norm specialization lemmas
on small explicit formulas. -/
def unitReplacementDesign {F : Type*} [Fintype F] {n : ℕ}
    (scope : F → Finset (Fin n)) : ReplacementDesign scope 1 1 0 1 0 :=
  let h := Fintype.card (ScopeIncidence scope)
  let eFin := Fintype.equivFin (ScopeIncidence scope)
  let place : ScopeIncidence scope → Fin h × AuxLabel 1 1 :=
    fun e => (eFin e, (fun _ => 0, fun _ => 0))
  have hinj : Function.Injective place := fun e₁ e₂ hEq =>
    eFin.injective (congrArg Prod.fst hEq)
  { varAssign := fun _ _ => 0
    factorAssign := fun _ _ => 0
    h := h
    place := place
    card_varGroup_le := fun t g => by
      have hsub : #(varGroup (fun (_ : Fin n) (_ : Fin 1) => (0 : Fin 1)) t g) ≤ n := by
        simpa only [card_univ, Fintype.card_fin] using
          card_le_univ (varGroup (fun (_ : Fin n) (_ : Fin 1) => (0 : Fin 1)) t g)
      omega
    factorAssign_of_empty := fun _ _ _ => rfl
    injective_place := hinj
    place_snd := fun _ => rfl
    h_mul_D_le := by
      change Fintype.card (ScopeIncidence scope) * 1 ^ (2 * 1) ≤ 2 * ∑ f : F, #(scope f)
      rw [card_scopeIncidence]
      omega
    total_measurement_rows_le := by
      have hmeas : #(measurementIndices 1 1 0 1) = 0 := by decide
      simp [hmeas]
    sum_abs_measurement_row_le :=
      sum_abs_varMeasurementMatrix_le 1 1 0 1 hinj (scopeVarOf scope)
    natDegree_replacementRow_le :=
      natDegree_varReplacementRow_le 1 1 0 1 place (scopeVarOf scope)
    eval_replacementRow_zero :=
      eval_varReplacementRow_zero 1 1 0 1 hinj (scopeVarOf scope)
    evalReplacementRow_nodePoint_eq_zero_of_kernel := fun e t g hg ξ hsupp hker =>
      evalVarReplacementRow_nodePoint_eq_zero_of_kernel 1 1 0 1 place (scopeVarOf scope)
        (fun _ _ => 0) (fun _ => rfl) e t g hg ξ hsupp hker
    map_replacementRowScaledInt :=
      map_varReplacementRowScaledInt 1 1 0 1 place (scopeVarOf scope)
    sum_coeffNorm1_replacementRowScaledInt_le :=
      sum_coeffNorm1_varReplacementRowScaledInt_le (by decide) hinj (scopeVarOf scope)
        (by intro a ha; omega) }

/-- Explicit equivalence between the unbranched variables `{0, 2}` (`univ \ {1}` in `Fin 3`) and
`Fin 2`. -/
def sampleFreeVarEquiv : ↥((univ : Finset (Fin 3)) \ ({1} : Finset (Fin 3))) ≃ Fin 2 where
  toFun v := if v.1 = 0 then 0 else 1
  invFun i := if i = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  left_inv := by decide
  right_inv := by decide

/-- Checked client of `commonZeroCount_eq_sum_branch_emod_ediv_design` on `sampleEqs` with partial
branching set `S = {1}` (branching on variable `1 : Fin 3` and leaving `{0, 2} ≃ Fin 2` free):
the branch-summed `ReplacementDesign` recovery equals the exact count `2`. -/
example :
    ∑ b ∈ branchAssignments ({1} : Finset (Fin 3)),
      ((univariateClearedParityTruncatedSum (univ : Finset (Fin 2))
        (fun i => relabelRestrictedMonomials ({1} : Finset (Fin 3)) sampleFreeVarEquiv b
          (sampleEqs i))
        (commonDenom 1 1 : ℤ) 2 (branchPrecision 3)
        (designReplacementScaledIntMap
          (unitReplacementDesign
            (augmentedEquationScope fun i =>
              relabelRestrictedMonomials ({1} : Finset (Fin 3)) sampleFreeVarEquiv b
                (sampleEqs i)))
          Sum.inl)).eval 0 /
          clearedProductDenom (commonDenom 1 1 : ℤ) 2 (branchPrecision 3)
            #(univ : Finset (Fin 2))) %
              ((2 : ℤ) ^ branchPrecision 3) = 2 := by
  have hrec := commonZeroCount_eq_sum_branch_emod_ediv_design
    ({1} : Finset (Fin 3)) sampleFreeVarEquiv (univ : Finset (Fin 2)) sampleEqs (k := 2)
    (fun b => augmentedEquationScope fun i =>
      relabelRestrictedMonomials ({1} : Finset (Fin 3)) sampleFreeVarEquiv b (sampleEqs i))
    (fun b => unitReplacementDesign
      (augmentedEquationScope fun i =>
        relabelRestrictedMonomials ({1} : Finset (Fin 3)) sampleFreeVarEquiv b (sampleEqs i)))
    (fun _ => Sum.inl)
    (by decide)
  have hcount : commonZeroCount (univ : Finset (Fin 2)) sampleEqs = 2 := by decide
  rw [← hrec, hcount]
  rfl

/-- Concrete degree and `coeffNorm1` bounds on `sampleEqs` via `unitReplacementDesign`: at degree
bound `k = 2` and precision `ℓ = 4`, the truncated sum has `natDegree = 0` (`≤ 0`) and every
coordinate polynomial has `coeffNorm1` bounded by
`2 ^ 3 * (4 * E_ℓ * (2 * designRowNormBound 1 1 ^ 2 + commonDenom 1 1 ^ 2) ^ 7) ^ 2`. -/
example {E_ℓ : ℕ} (hE : ∀ j < 4, (Polynomial.parityBaseDigit 4 j).coeffNorm1 ≤ E_ℓ) (s : ℕ) :
    (univariateClearedParityTruncatedSum (univ : Finset (Fin 2)) sampleEqs
      (commonDenom 1 1 : ℤ) 2 4
      (designReplacementScaledIntMap
        (unitReplacementDesign (augmentedEquationScope sampleEqs)) Sum.inl)).natDegree ≤ 0 ∧
    (univariateClearedParityCoord (univ : Finset (Fin 2)) sampleEqs
      (commonDenom 1 1 : ℤ) 2 4
      (designReplacementScaledIntMap
        (unitReplacementDesign (augmentedEquationScope sampleEqs)) Sum.inl) s).coeffNorm1 ≤
      2 ^ 3 *
        (4 * E_ℓ *
          (2 * designRowNormBound 1 1 ^ 2 + commonDenom 1 1 ^ 2) ^ (2 * 4 - 1)) ^ 2 := by
  refine ⟨?_, ?_⟩
  · simpa using natDegree_univariateClearedParityTruncatedSum_design_le
      (unitReplacementDesign (augmentedEquationScope sampleEqs)) Sum.inl
      (univ : Finset (Fin 2)) sampleEqs 2 4 (by decide)
  · simpa using coeffNorm1_univariateClearedParityCoord_design_le
      (unitReplacementDesign (augmentedEquationScope sampleEqs)) Sum.inl
      (univ : Finset (Fin 2)) sampleEqs 2 4 (S_mon := 2) (by decide) (by decide) hE s

/-- Empty equation family on `n = 16384` variables used to witness
`exists_replacementDesign_augmentedEquationScope` with `b₀ = 0` (`b = 1`), `w = 1`, `Q = 3`,
`r = 2`, `A₀ = 0`, `R = 2`, `τ = 1 / 2`. -/
def emptyEqs16384 : Fin 0 → Finset (Finset (Fin 16384)) :=
  Fin.elim0

/-- Nonvacuous witness of `exists_replacementDesign_augmentedEquationScope` and exact modular
recovery of `commonZeroCount = 2 ^ 16384` at precision `ℓ = 16385`. -/
theorem exists_design_and_recover_emptyEqs16384 :
    ∃ D : ReplacementDesign (augmentedEquationScope emptyEqs16384) 3 2 0 2 (1 / 2),
      ((univariateClearedParityTruncatedSum (univ : Finset (Fin 0)) emptyEqs16384
          (commonDenom 3 2 : ℤ) 3 16385
          (designReplacementScaledIntMap D Sum.inl)).eval 0 /
        clearedProductDenom (commonDenom 3 2 : ℤ) 3 16385 #(univ : Finset (Fin 0))) %
          ((2 : ℤ) ^ 16385) =
        (2 : ℤ) ^ 16384 := by
  have hcard : #(measurementIndices 3 2 0 2) = 10 := by
    rw [card_measurementIndices_eq]
    decide
  have htail : binomTailProb 3 2 0 2 ≤ (1 / 2 : ℚ) / ((2 : ℚ) * ((0 + 1 : ℕ) : ℚ)) := by
    rw [binomTailProb_eq_div 3 2 0 2 (by decide), hcard]
    norm_num
  have hne : Nonempty (ReplacementDesign (augmentedEquationScope emptyEqs16384) 3 2 0 2 (1 / 2)) :=
    exists_replacementDesign_augmentedEquationScope emptyEqs16384 (b₀ := 0) (w := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num)
      (by intro a ha; omega)
      (fun v => by simp)
      (fun i => Fin.elim0 i)
      (by decide)
      (by decide)
      htail
  obtain ⟨D⟩ := hne
  refine ⟨D, ?_⟩
  have hrec :=
    emod_ediv_eval_zero_clearedParityTruncatedSum_design_eq_commonZeroCount D Sum.inl
      (univ : Finset (Fin 0)) emptyEqs16384 (k := 3) (ℓ := 16385) (by decide)
      (fun i => Fin.elim0 i)
  have hcount : (commonZeroCount (univ : Finset (Fin 0)) emptyEqs16384 : ℤ) = (2 : ℤ) ^ 16384 := by
    have hempty : (univ : Finset (Fin 0)) = ∅ := rfl
    rw [hempty, commonZeroCount_empty, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  exact hrec.trans hcount

end Cslib.BitString.SparseReplacementDesignTests
