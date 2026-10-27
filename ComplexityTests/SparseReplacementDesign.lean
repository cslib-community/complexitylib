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

Concrete checks and nonvacuous witnesses for `withNeutralScope` equation scopes,
`designRowNormBound`, `exists_replacementDesign_withNeutralScope`, nonconstant factor locality
(`eval_univariateMonomialSumPoly_designReplacementMap_nodePoint_eq`), and the
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

/-- Scope family of `sampleEqs`. -/
def sampleScope (i : Fin 2) : Finset (Fin 3) :=
  equationScope (sampleEqs i)

/-- Expected-value control: `sampleEqs` has `commonZeroCount = 2`, while the empty equation set has
`commonZeroCount = 8`. -/
example :
    commonZeroCount univ sampleEqs = 2 ∧
    commonZeroCount (∅ : Finset (Fin 2)) sampleEqs = 8 := by
  decide

/-- Total incidence of `withNeutralScope sampleScope` is `(2 + 2) + 3 = 7 ≥ 3`. -/
example :
    totalIncidence (withNeutralFactors (univ : Finset (Fin 2))) (withNeutralScope sampleScope) = 7 ∧
      3 ≤ totalIncidence (withNeutralFactors (univ : Finset (Fin 2)))
        (withNeutralScope sampleScope) := by
  refine ⟨?_, card_le_totalIncidence_withNeutralFactors (univ : Finset (Fin 2)) sampleScope⟩
  rw [totalIncidence_withNeutralFactors]
  decide

/-- Variable `1 : Fin 3` belongs to both equation scopes plus its neutral singleton scope
(`2 + 1 = 3` scopes total), whereas variable `0 : Fin 3` belongs to `1 + 1 = 2` scopes. -/
example :
    varIncidence (withNeutralFactors (univ : Finset (Fin 2))) (withNeutralScope sampleScope) 1 = 3 ∧
      varIncidence (withNeutralFactors (univ : Finset (Fin 2)))
        (withNeutralScope sampleScope) 0 = 2 := by
  rw [varIncidence_withNeutralFactors, varIncidence_withNeutralFactors]
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

/-- Explicit `Q = 1, r = 2, A₀ = 0, R = 2, τ = 0` replacement design on
`withNeutralScope sampleScope` (`n = 3`, `h = 3`):
- variables `0, 1` are in group `0` and variable `2` is in group `1`,
- both equation factors `Sum.inl 0` and `Sum.inl 1` are assigned to group `0`,
- `measurementIndices 1 2 0 2 = ∅`, so measurement vectors vanish unconditionally,
- for variable `2` in equation `1` (`scope = {1, 2}`), the replacement polynomial evaluates to `1`
  at `T = 0` and `0` at `T = nodePoint 0 = 1`, hence is nonconstant of exact degree `1`. -/
def nonconstSampleVarAssign : Fin 3 → Fin 1 → Fin 2 :=
  fun v _ => if v.1 < 2 then 0 else 1

/-- Factor group schedule for `nonconstSampleDesign`. -/
def nonconstSampleFactorAssign : Fin 2 ⊕ Fin 3 → Fin 1 → Fin 2
  | Sum.inl _, _ => 0
  | Sum.inr _, _ => 1

/-- Copy index in `Fin 3` separating the `7` incidences of `withNeutralScope sampleScope` into
distinct `(copy, AuxLabel 1 2)` slots. -/
def nonconstSampleCopy (e : ScopeIncidence (withNeutralScope sampleScope)) : Fin 3 :=
  match e.1 with
  | Sum.inl 0 => if e.2.1 = 0 then 0 else 1
  | Sum.inl 1 => if e.2.1 = 1 then 2 else 0
  | Sum.inr 0 => 0
  | Sum.inr 1 => 1
  | Sum.inr 2 => 0

/-- Injective placement for `nonconstSampleDesign`. -/
def nonconstSamplePlace (e : ScopeIncidence (withNeutralScope sampleScope)) :
    Fin 3 × AuxLabel 1 2 :=
  (nonconstSampleCopy e,
    (nonconstSampleVarAssign (scopeVarOf (withNeutralScope sampleScope) e),
     nonconstSampleFactorAssign (scopeFactorOf (withNeutralScope sampleScope) e)))

theorem injective_nonconstSamplePlace : Function.Injective nonconstSamplePlace := by
  decide

/-- Concrete `Q = 1, r = 2, A₀ = 0, R = 2, τ = 0` replacement design on
`withNeutralScope sampleScope` with nonconstant degree-`1` replacement rows. -/
def nonconstSampleDesign :
    ReplacementDesign (withNeutralScope sampleScope) 1 2 0 2 0 where
  varAssign := nonconstSampleVarAssign
  factorAssign := nonconstSampleFactorAssign
  h := 3
  place := nonconstSamplePlace
  card_varGroup_le := by decide
  factorAssign_of_empty := by decide
  injective_place := injective_nonconstSamplePlace
  place_snd := fun _ => rfl
  h_mul_D_le := by decide
  total_measurement_rows_le := by
    have hmeas : #(measurementIndices 1 2 0 2) = 0 := by decide
    simp [hmeas]
  sum_abs_measurement_row_le :=
    sum_abs_varMeasurementMatrix_le 1 2 0 2 injective_nonconstSamplePlace
      (scopeVarOf (withNeutralScope sampleScope))
  natDegree_replacementRow_le :=
    natDegree_varReplacementRow_le 1 2 0 2 nonconstSamplePlace
      (scopeVarOf (withNeutralScope sampleScope))
  eval_replacementRow_zero :=
    eval_varReplacementRow_zero 1 2 0 2 injective_nonconstSamplePlace
      (scopeVarOf (withNeutralScope sampleScope))
  evalReplacementRow_nodePoint_eq_zero_of_kernel := fun e t g hg ξ hsupp hker =>
    evalVarReplacementRow_nodePoint_eq_zero_of_kernel 1 2 0 2 nonconstSamplePlace
      (scopeVarOf (withNeutralScope sampleScope)) nonconstSampleVarAssign (fun _ => rfl) e t g hg
      ξ hsupp hker
  map_replacementRowScaledInt :=
    map_varReplacementRowScaledInt 1 2 0 2 nonconstSamplePlace
      (scopeVarOf (withNeutralScope sampleScope))
  sum_coeffNorm1_replacementRowScaledInt_le :=
    sum_coeffNorm1_varReplacementRowScaledInt_le (by decide) injective_nonconstSamplePlace
      (scopeVarOf (withNeutralScope sampleScope)) (by intro a ha; omega)

/-- Assignment `x₁ = (false, false, true)` placing `true` on variable `2 : Fin 3` in group `1` and
`false` on group `0 = {0, 1}`. -/
def sampleAssign₁ : Fin 3 → Bool := fun v => decide (v = 2)

/-- All-false assignment `x₂ = (false, false, false)` agreeing with `sampleAssign₁` on group
`0 = {0, 1}` and differing on variable `2 ∈ equationScope (sampleEqs 1)`. -/
def sampleAssign₂ : Fin 3 → Bool := fun _ => false

/-- Nonconstant replacement-row and factor-locality control on `nonconstSampleDesign`:
1. For equation `1` (`x₁ x₂ + 1`, scope `{1, 2}`) and variable `2` on `sampleAssign₁`, the
   replacement polynomial
   `P(T) = designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₁ 1 2`
   evaluates to `1` at `T = 0` and to `0` at `T = nodePoint (0 : Fin 1)` (comparing `sampleAssign₁`
   with `sampleAssign₂` on group `0`), so `P.eval 0 ≠ P.eval (nodePoint 0)` and `P` has exact
   nonconstant degree `P.natDegree = 1`.
2. Although `sampleAssign₁` and `sampleAssign₂` differ on variable
   `2 ∈ equationScope (sampleEqs 1)`,
   `eval_univariateMonomialSumPoly_designReplacementMap_nodePoint_eq` proves unconditionally that
   their substituted equation-`1` factors at `nodePoint (0 : Fin 1)` coincide. -/
example :
    (designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₁ 1 2).eval 0 = 1 ∧
    (designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₁ 1 2).eval
      (nodePoint (0 : Fin 1)) = 0 ∧
    (designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₁ 1 2).natDegree = 1 ∧
    (univariateMonomialSumPoly ℚ (designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₁ 1)
      (sampleEqs 1)).eval (nodePoint (0 : Fin 1)) =
    (univariateMonomialSumPoly ℚ (designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₂ 1)
      (sampleEqs 1)).eval (nodePoint (0 : Fin 1)) := by
  have hgrp : ∀ u ∈ varGroup nonconstSampleDesign.varAssign (0 : Fin 1)
      (nonconstSampleDesign.factorAssign (Sum.inl 1) (0 : Fin 1)),
      sampleAssign₁ u = sampleAssign₂ u := by
    decide
  have hmeas :
      (varMeasurementMatrix 1 2 0 2 ℚ nonconstSampleDesign.place
        (scopeVarOf (withNeutralScope sampleScope))).mulVec
          (fun u => bitVal ℚ (sampleAssign₁ u)) =
      (varMeasurementMatrix 1 2 0 2 ℚ nonconstSampleDesign.place
        (scopeVarOf (withNeutralScope sampleScope))).mulVec
          (fun u => bitVal ℚ (sampleAssign₂ u)) := by
    funext p
    exact absurd p.2.2 (by decide +revert)
  have heval0 :
      (designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₁ 1 2).eval 0 = 1 := by
    rw [eval_zero_designReplacementMap]
    rfl
  have heval1 :
      (designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₁ 1 2).eval
        (nodePoint (0 : Fin 1)) = 0 := by
    have hloc := eval_nodePoint_designReplacementMap_eq_of_eq_on_varGroup
      nonconstSampleDesign Sum.inl (i := (1 : Fin 2)) (v := (2 : Fin 3)) (by decide)
      (0 : Fin 1) sampleAssign₁ sampleAssign₂ hgrp hmeas
    have hzero :
        designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₂ 1 2 = 0 := by
      simp [sampleAssign₂, designReplacementMap, evalVarReplacementRowPoly]
    rw [hloc, hzero, Polynomial.eval_zero]
  have hdeg :
      (designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₁ 1 2).natDegree = 1 := by
    have hle :
        (designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₁ 1 2).natDegree ≤ 2 - 1 :=
      natDegree_designReplacementMap_le nonconstSampleDesign Sum.inl sampleAssign₁ 1 2
    have hne0 :
        (designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₁ 1 2).natDegree ≠ 0 := by
      intro h0
      have hconst := Polynomial.eq_C_of_natDegree_eq_zero h0
      have h1 :
          (designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₁ 1 2).eval 0 =
          (designReplacementMap nonconstSampleDesign Sum.inl sampleAssign₁ 1 2).eval
            (nodePoint (0 : Fin 1)) := by
        conv_lhs => rw [hconst, Polynomial.eval_C]
        conv_rhs => rw [hconst, Polynomial.eval_C]
      rw [heval0, heval1] at h1
      exact one_ne_zero h1
    omega
  refine ⟨heval0, heval1, hdeg, ?_⟩
  exact eval_univariateMonomialSumPoly_designReplacementMap_nodePoint_eq
    nonconstSampleDesign Sum.inl sampleEqs (i := (1 : Fin 2)) (by decide) (0 : Fin 1)
    sampleAssign₁ sampleAssign₂ hgrp hmeas

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
            (withNeutralScope fun i =>
              equationScope
                (relabelRestrictedMonomials ({1} : Finset (Fin 3)) sampleFreeVarEquiv b
                  (sampleEqs i))))
          Sum.inl)).eval 0 /
          clearedProductDenom (commonDenom 1 1 : ℤ) 2 (branchPrecision 3)
            #(univ : Finset (Fin 2))) %
              ((2 : ℤ) ^ branchPrecision 3) = 2 := by
  have hrec := commonZeroCount_eq_sum_branch_emod_ediv_design
    ({1} : Finset (Fin 3)) sampleFreeVarEquiv (univ : Finset (Fin 2)) sampleEqs (k := 2)
    (fun b => withNeutralScope fun i =>
      equationScope
        (relabelRestrictedMonomials ({1} : Finset (Fin 3)) sampleFreeVarEquiv b (sampleEqs i)))
    (fun b => unitReplacementDesign
      (withNeutralScope fun i =>
        equationScope
          (relabelRestrictedMonomials ({1} : Finset (Fin 3)) sampleFreeVarEquiv b (sampleEqs i))))
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
        (unitReplacementDesign (withNeutralScope sampleScope)) Sum.inl)).natDegree ≤ 0 ∧
    (univariateClearedParityCoord (univ : Finset (Fin 2)) sampleEqs
      (commonDenom 1 1 : ℤ) 2 4
      (designReplacementScaledIntMap
        (unitReplacementDesign (withNeutralScope sampleScope)) Sum.inl) s).coeffNorm1 ≤
      2 ^ 3 *
        (4 * E_ℓ *
          (2 * designRowNormBound 1 1 ^ 2 + commonDenom 1 1 ^ 2) ^ (2 * 4 - 1)) ^ 2 := by
  refine ⟨?_, ?_⟩
  · simpa using natDegree_univariateClearedParityTruncatedSum_design_le
      (unitReplacementDesign (withNeutralScope sampleScope)) Sum.inl
      (univ : Finset (Fin 2)) sampleEqs 2 4 (by decide)
  · simpa using coeffNorm1_univariateClearedParityCoord_design_le
      (unitReplacementDesign (withNeutralScope sampleScope)) Sum.inl
      (univ : Finset (Fin 2)) sampleEqs 2 4 (S_mon := 2) (by decide) (by decide) hE s

/-- Empty equation family on `n = 16384` variables used to witness
`exists_replacementDesign_withNeutralScope` with `b₀ = 0` (`b = 1`), `w = 1`, `Q = 3`,
`r = 2`, `A₀ = 0`, `R = 2`, `τ = 1 / 2`. -/
def emptyEqs16384 : Fin 0 → Finset (Finset (Fin 16384)) :=
  Fin.elim0

/-- Nonvacuous witness of `exists_replacementDesign_withNeutralScope` and exact modular
recovery of `commonZeroCount = 2 ^ 16384` at precision `ℓ = 16385`. -/
theorem exists_design_and_recover_emptyEqs16384 :
    ∃ D : ReplacementDesign (withNeutralScope fun i => equationScope (emptyEqs16384 i))
        3 2 0 2 (1 / 2),
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
  have hne : Nonempty (ReplacementDesign
      (withNeutralScope fun i => equationScope (emptyEqs16384 i)) 3 2 0 2 (1 / 2)) :=
    exists_replacementDesign_withNeutralScope (fun i => equationScope (emptyEqs16384 i))
      (b₀ := 0) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num)
      (by intro a ha; omega)
      (fun v => by simp [varIncidence])
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
