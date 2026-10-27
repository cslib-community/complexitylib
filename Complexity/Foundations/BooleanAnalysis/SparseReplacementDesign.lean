/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseClearedSpecialization
public import Complexity.Foundations.LinearAlgebra.ReplacementDesign

/-!
# Instantiating cleared parity-polynomial specialization with Section 4 replacement designs

This module connects the Section 4 algebraic replacement design construction
(`Complexity.Foundations.LinearAlgebra.ReplacementDesign`) directly to the Section 5.3–5.5 and
Appendix B.2–B.3 cleared-denominator parity-polynomial zero-counting pipeline
(`Complexity.Foundations.BooleanAnalysis.SparseClearedSpecialization`) of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (printed pp. 32–34, 37–39,
48–50):

1. **Neutral singleton scope augmentation (§5.3 & §5.5, pp. 37–38)**:
   Given an equation family `P : κ → Finset (Finset (Fin n))`, `augmentedEquationScope P` augments
   the equation scopes `equationScope (P i)` (`Sum.inl i`) with one singleton scope `{v}`
   (`Sum.inr v`) per variable `v : Fin n`. This ensures that every variable occurs in at least one
   factor scope, that the total incidence count is `(∑ i, #(equationScope (P i))) + n ≥ n`
   (`sum_card_augmentedEquationScope`, `le_sum_card_augmentedEquationScope`), and that per-variable
   factor occurrences increase by exactly `1` (`card_filter_mem_augmentedEquationScope`), so
   Lemma 4.7 (`exists_replacementDesign`) applies directly whenever equation occurrences are bounded
   by `b₀` and equation scopes by `w ≥ 1` (`exists_replacementDesign_augmentedEquationScope`).

2. **Univariate polynomial replacement rows from a `ReplacementDesign` (§5.3–5.4, pp. 37–38)**:
   For any `D : ReplacementDesign scope Q r A₀ R τ`, incidence `e : ScopeIncidence scope`, and
   Boolean assignment `x : Fin n → Bool`, `evalVarReplacementRowPoly D e x : ℚ[X]` and its scaled
   integer counterpart `evalVarReplacementRowScaledIntPoly D e x : ℤ[X]` evaluate `D`'s replacement
   rows on the `{0, 1}` vector `fun u => bitVal _ (x u)`. Using `D`'s fields from Definition 3.1
   and Lemma 4.6, we prove:
   - `(evalVarReplacementRowScaledIntPoly D e x).map (Int.castRingHom ℚ) =
     C (commonDenom Q R : ℚ) * evalVarReplacementRowPoly D e x`,
   - `(evalVarReplacementRowPoly D e x).eval 0 = bitVal ℚ (x (scopeVarOf scope e))` and
     `(evalVarReplacementRowScaledIntPoly D e x).eval 0 =
     (commonDenom Q R : ℤ) * bitVal ℤ (x (scopeVarOf scope e))`,
   - `natDegree ≤ R - 1` for both polynomials,
   - `(evalVarReplacementRowScaledIntPoly D e x).coeffNorm1 ≤ designRowNormBound Q R`, where
     `designRowNormBound Q R = commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (4 * Q) ^ (R - 1))`, and
   - at each evaluation node `nodePoint t` (`t : Fin Q`), `(evalVarReplacementRowPoly D e x).eval
     (nodePoint t)` depends only on `x` restricted to the assigned variable group
     `varGroup D.varAssign t (D.factorAssign (scopeFactorOf scope e) t)` and the measurement vector
     `(varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec
     (fun u => bitVal ℚ (x u))`.

3. **Concrete §5.3–5.5 degree, norm, and exact modular zero-counting theorems**:
   Packaging these replacement rows into `designReplacementMap D emb` and
   `designReplacementScaledIntMap D emb` (for any factor embedding `emb : κ → F`) discharges all
   clearing, degree, $T = 0$ evaluation, and `coeffNorm1` premises of
   `SparseClearedSpecialization`, yielding concrete `ReplacementDesign` specializations of:
   - the equation (5.5a) degree bound `(k * (R - 1)) * (#I + 2 * (ℓ - 1))`
     (`natDegree_univariateClearedParityCoord_design_le`,
     `natDegree_univariateClearedParityTruncatedSum_design_le`),
   - the rational homogenization identity $\tilde{H}_s(T) = \Omega [V^s] H(T)$ over `ℚ[X]`
     (`map_univariateClearedParityCoord_design`,
     `map_univariateClearedParityTruncatedSum_design`),
   - the Appendix B.2 coordinate `ℓ₁`-norm bound
     (`coeffNorm1_univariateClearedParityCoord_design_le`),
   - exact integer division and modulo-`2 ^ ℓ` recovery of `commonZeroCount I P` when `n < ℓ` and
     `∀ i ∈ I, ∀ M ∈ P i, #M ≤ k`, including Cramer's rule determinant recovery (when `D_H ≠ 0`)
     and §5.5 heavy-variable branch summation at shared precision `branchPrecision n = n + 1`
     (`emod_sum_ediv_eval_zero_clearedParityCoord_design_eq_commonZeroCount`,
     `emod_ediv_eval_zero_clearedParityTruncatedSum_design_eq_commonZeroCount`,
     `emod_sum_cramer_ediv_design_eq_commonZeroCount`,
     `commonZeroCount_eq_sum_branch_emod_ediv_design`).

## Main definitions

* `Cslib.BitString.augmentedEquationScope`: scope family on `κ ⊕ Fin n` combining
  `equationScope (P i)` with neutral singleton scopes `{v}`.
* `Cslib.BitString.designRowNormBound`: the Lemma 4.6 row `ℓ₁`-norm bound
  `commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (4 * Q) ^ (R - 1))`.
* `Cslib.BitString.evalVarReplacementRowPoly`,
  `Cslib.BitString.evalVarReplacementRowScaledIntPoly`: univariate rational and scaled integer
  replacement polynomials evaluated on a Boolean assignment `x : Fin n → Bool`.
* `Cslib.BitString.designReplacementMap`,
  `Cslib.BitString.designReplacementScaledIntMap`: equation-indexed rational and scaled integer
  replacement polynomial families associated to a `ReplacementDesign`.

## Main results

* `Cslib.BitString.sum_card_augmentedEquationScope`,
  `Cslib.BitString.card_filter_mem_augmentedEquationScope`,
  `Cslib.BitString.exists_replacementDesign_augmentedEquationScope`: incidence count, variable
  occurrence count, and Lemma 4.7 existence for neutral-singleton augmented equation scopes.
* `Cslib.BitString.map_evalVarReplacementRowScaledIntPoly`,
  `Cslib.BitString.eval_zero_evalVarReplacementRowPoly`,
  `Cslib.BitString.eval_zero_evalVarReplacementRowScaledIntPoly`,
  `Cslib.BitString.natDegree_evalVarReplacementRowScaledIntPoly_le`,
  `Cslib.BitString.coeffNorm1_evalVarReplacementRowScaledIntPoly_le`,
  `Cslib.BitString.eval_evalVarReplacementRowPoly_nodePoint_eq_of_eq_on_varGroup`:
  Definition 3.1 and Lemma 4.6 properties of `evalVarReplacementRowPoly` and
  `evalVarReplacementRowScaledIntPoly`.
* `Cslib.BitString.natDegree_univariateClearedParityCoord_design_le`,
  `Cslib.BitString.natDegree_univariateClearedParityTruncatedSum_design_le`,
  `Cslib.BitString.map_univariateClearedParityCoord_design`,
  `Cslib.BitString.coeffNorm1_univariateClearedParityCoord_design_le`:
  concrete `ReplacementDesign` degree, homogenization, and `ℓ₁`-norm bounds.
* `Cslib.BitString.emod_sum_ediv_eval_zero_clearedParityCoord_design_eq_commonZeroCount`,
  `Cslib.BitString.emod_ediv_eval_zero_clearedParityTruncatedSum_design_eq_commonZeroCount`,
  `Cslib.BitString.emod_sum_cramer_ediv_design_eq_commonZeroCount`,
  `Cslib.BitString.commonZeroCount_eq_sum_branch_emod_ediv_design`:
  exact integer division recovery of `commonZeroCount` from `ReplacementDesign`s on a single system
  and summed across heavy-variable branches.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (Sections 4.5–4.6, 5.3–5.5,
  and Appendix B.2–B.3, pp. 32–34, 37–39, 48–50)
-/

@[expose] public noncomputable section

namespace Cslib.BitString

open Finset Polynomial
open scoped BigOperators
open Cslib.BalancedSchedules Cslib.LinearAlgebra

variable {κ : Type*} {n Q r A₀ R : ℕ} {τ : ℚ}

/-! ### 1. Neutral singleton scope augmentation (§5.3 & §5.5, pp. 37–38) -/

/-- The augmented factor scope family on `κ ⊕ Fin n` combining the equation scopes
`equationScope (P i)` (`Sum.inl i`) with one neutral singleton scope `{v}` (`Sum.inr v`) per
variable `v : Fin n` (§5.3 and §5.5, printed pp. 37–38). -/
def augmentedEquationScope (P : κ → Finset (Finset (Fin n))) : κ ⊕ Fin n → Finset (Fin n)
  | Sum.inl i => equationScope (P i)
  | Sum.inr v => {v}

@[simp]
theorem augmentedEquationScope_inl (P : κ → Finset (Finset (Fin n))) (i : κ) :
    augmentedEquationScope P (Sum.inl i) = equationScope (P i) :=
  rfl

@[simp]
theorem augmentedEquationScope_inr (P : κ → Finset (Finset (Fin n))) (v : Fin n) :
    augmentedEquationScope P (Sum.inr v) = {v} :=
  rfl

/-- Every variable `v ∈ M` of a monomial `M ∈ P i` belongs to
`augmentedEquationScope P (Sum.inl i)`. -/
theorem mem_augmentedEquationScope_inl_of_mem {P : κ → Finset (Finset (Fin n))} {i : κ}
    {M : Finset (Fin n)} {v : Fin n} (hM : M ∈ P i) (hv : v ∈ M) :
    v ∈ augmentedEquationScope P (Sum.inl i) :=
  mem_biUnion.mpr ⟨M, hM, hv⟩

/-- The total incidence count of `augmentedEquationScope P` equals
`(∑ i : κ, #(equationScope (P i))) + n`. -/
theorem sum_card_augmentedEquationScope [Fintype κ] (P : κ → Finset (Finset (Fin n))) :
    (∑ f : κ ⊕ Fin n, #(augmentedEquationScope P f)) =
      (∑ i : κ, #(equationScope (P i))) + n := by
  simp only [Fintype.sum_sum_type, augmentedEquationScope_inl, augmentedEquationScope_inr,
    card_singleton, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- Neutral singleton factors ensure that the total incidence count of `augmentedEquationScope P`
is at least `n` (§5.5, p. 38: `M' ≥ n'`). -/
theorem le_sum_card_augmentedEquationScope [Fintype κ] (P : κ → Finset (Finset (Fin n))) :
    n ≤ ∑ f : κ ⊕ Fin n, #(augmentedEquationScope P f) := by
  rw [sum_card_augmentedEquationScope]
  exact Nat.le_add_left n _

/-- If `1 ≤ w` and every equation scope `equationScope (P i)` has size at most `w`, then every
scope in `augmentedEquationScope P` has size at most `w`. -/
theorem card_augmentedEquationScope_le {P : κ → Finset (Finset (Fin n))} {w : ℕ}
    (hw1 : 1 ≤ w) (hw : ∀ i : κ, #(equationScope (P i)) ≤ w) (f : κ ⊕ Fin n) :
    #(augmentedEquationScope P f) ≤ w := by
  cases f with
  | inl i => exact hw i
  | inr v => simpa only [augmentedEquationScope_inr, card_singleton] using hw1

/-- Each variable `v : Fin n` occurs in `#{i : κ | v ∈ equationScope (P i)} + 1` scopes of
`augmentedEquationScope P` (its equation occurrences plus its neutral singleton scope). -/
theorem card_filter_mem_augmentedEquationScope [Fintype κ]
    (P : κ → Finset (Finset (Fin n))) (v : Fin n) :
    #{f : κ ⊕ Fin n | v ∈ augmentedEquationScope P f} =
      #{i : κ | v ∈ equationScope (P i)} + 1 := by
  rw [card_filter, card_filter, Fintype.sum_sum_type]
  simp only [augmentedEquationScope_inl, augmentedEquationScope_inr, mem_singleton, sum_ite_eq,
    mem_univ, ↓reduceIte]
  congr 1

/-- If every variable occurs in at most `b₀` equation scopes, then every variable occurs in at most
`b₀ + 1` scopes of `augmentedEquationScope P`. -/
theorem card_filter_mem_augmentedEquationScope_le [Fintype κ]
    {P : κ → Finset (Finset (Fin n))} {b₀ : ℕ}
    (hb : ∀ v : Fin n, #{i : κ | v ∈ equationScope (P i)} ≤ b₀) (v : Fin n) :
    #{f : κ ⊕ Fin n | v ∈ augmentedEquationScope P f} ≤ b₀ + 1 := by
  rw [card_filter_mem_augmentedEquationScope]
  exact Nat.add_le_add_right (hb v) 1

/-- If every variable occurs in at most `b₀` equation scopes, then the total incidence count of
`augmentedEquationScope P` is at most `(b₀ + 1) * n`. -/
theorem sum_card_augmentedEquationScope_le [Fintype κ]
    {P : κ → Finset (Finset (Fin n))} {b₀ : ℕ}
    (hb : ∀ v : Fin n, #{i : κ | v ∈ equationScope (P i)} ≤ b₀) :
    (∑ f : κ ⊕ Fin n, #(augmentedEquationScope P f)) ≤ (b₀ + 1) * n := by
  classical
  have hswap :
      (∑ f : κ ⊕ Fin n, #(augmentedEquationScope P f)) =
        ∑ v : Fin n, #{f : κ ⊕ Fin n | v ∈ augmentedEquationScope P f} := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun f _ => ?_
    simp only [sum_ite_mem, univ_inter]
  rw [hswap]
  calc
    (∑ v : Fin n, #{f : κ ⊕ Fin n | v ∈ augmentedEquationScope P f})
      ≤ ∑ _v : Fin n, (b₀ + 1) :=
        sum_le_sum fun v _ => card_filter_mem_augmentedEquationScope_le hb v
    _ = (b₀ + 1) * n := by
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

/-- **Lemma 4.7 for neutral-singleton augmented equation scopes (§5.5, pp. 38–39)**:
when every variable belongs to at most `b₀` equation scopes and every equation scope has size at
most `w` (`1 ≤ w`), the augmented scope family `augmentedEquationScope P` satisfies `1 ≤ b₀ + 1`
and `M ≤ (b₀ + 1) * n` automatically, and admits a Section 4 `ReplacementDesign` under the balance
and binomial-tail conditions for `b = b₀ + 1`. -/
theorem exists_replacementDesign_augmentedEquationScope [Fintype κ]
    (P : κ → Finset (Finset (Fin n))) {b₀ w : ℕ}
    (hn : 1 ≤ n) (hw_pos : 1 ≤ w)
    (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q) (hτ : 0 ≤ τ)
    (hI : ∀ a < R - 1, A₀ + a ≤ Q)
    (hb : ∀ v : Fin n, #{i : κ | v ∈ equationScope (P i)} ≤ b₀)
    (hw : ∀ i : κ, #(equationScope (P i)) ≤ w)
    (hincidenceSize :
      2 * (b₀ + 1 + w) * (r ^ (2 * Q)) ^ 2 ≤ (∑ i : κ, #(equationScope (P i))) + n)
    (hgroupSize : 2 * Q * r ^ 2 ≤ n)
    (htail : binomTailProb Q r A₀ R ≤ τ / ((r : ℚ) * ((b₀ + 1 : ℕ) : ℚ))) :
    Nonempty (ReplacementDesign (augmentedEquationScope P) Q r A₀ R τ) := by
  refine exists_replacementDesign (augmentedEquationScope P) hn (Nat.le_add_left 1 b₀) hw_pos hr
    hR hRQ hτ hI (card_filter_mem_augmentedEquationScope_le hb)
    (card_augmentedEquationScope_le hw_pos hw) (sum_card_augmentedEquationScope_le hb) ?_ hgroupSize
    htail
  rwa [sum_card_augmentedEquationScope]

/-! ### 2. Univariate replacement polynomials from a `ReplacementDesign` (§5.3–5.4, pp. 37–38) -/

/-- The explicit Lemma 4.6 `ℓ₁` coefficient norm bound
`commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (4 * Q) ^ (R - 1))` for scaled integer replacement rows
(printed p. 33). -/
def designRowNormBound (Q R : ℕ) : ℕ :=
  commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (4 * Q) ^ (R - 1))

/-- `commonDenom Q R ≤ designRowNormBound Q R`. -/
theorem commonDenom_le_designRowNormBound (Q R : ℕ) :
    commonDenom Q R ≤ designRowNormBound Q R :=
  Nat.le_mul_of_pos_right (commonDenom Q R) (by omega)

/-- `0 < designRowNormBound Q R`. -/
theorem designRowNormBound_pos (Q R : ℕ) : 0 < designRowNormBound Q R :=
  lt_of_lt_of_le (commonDenom_pos Q R) (commonDenom_le_designRowNormBound Q R)

/-- `(commonDenom Q R : ℤ) ≠ 0`. -/
theorem commonDenom_intCast_ne_zero (Q R : ℕ) : (commonDenom Q R : ℤ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (commonDenom_pos Q R).ne'

/-- `(commonDenom Q R : ℚ) ≠ 0`. -/
theorem commonDenom_ratCast_ne_zero (Q R : ℕ) : (commonDenom Q R : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (commonDenom_pos Q R).ne'

/-- The univariate rational replacement polynomial `⟨P⃗_e(T), x⟩ ∈ ℚ[X]` for incidence
`e : ScopeIncidence scope` evaluated on a Boolean assignment `x : Fin n → Bool` (§5.3, p. 37). -/
noncomputable def evalVarReplacementRowPoly {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ)
    (e : ScopeIncidence scope) (x : Fin n → Bool) : Polynomial ℚ :=
  ∑ u : Fin n,
    Polynomial.C (bitVal ℚ (x u)) * varReplacementRow Q r A₀ R D.place (scopeVarOf scope) e u

/-- The scaled integer univariate replacement polynomial `d_den ⟨P⃗_e(T), x⟩ ∈ ℤ[X]` for incidence
`e : ScopeIncidence scope` evaluated on a Boolean assignment `x : Fin n → Bool`
(§5.4 & Lemma 4.6, pp. 33, 37–38). -/
noncomputable def evalVarReplacementRowScaledIntPoly {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ)
    (e : ScopeIncidence scope) (x : Fin n → Bool) : Polynomial ℤ :=
  ∑ u : Fin n,
    Polynomial.C (bitVal ℤ (x u)) *
      varReplacementRowScaledInt Q r A₀ R D.place (scopeVarOf scope) e u

/-- Pointwise evaluation of `evalVarReplacementRowPoly D e x` at `t : ℚ` agrees with
`evalVarReplacementRow` on `fun u => bitVal ℚ (x u)`. -/
theorem eval_evalVarReplacementRowPoly {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ)
    (e : ScopeIncidence scope) (x : Fin n → Bool) (t : ℚ) :
    (evalVarReplacementRowPoly D e x).eval t =
      evalVarReplacementRow Q r A₀ R D.place (scopeVarOf scope) e t (fun u => bitVal ℚ (x u)) := by
  rw [evalVarReplacementRowPoly, evalVarReplacementRow, Polynomial.eval_finsetSum]
  refine sum_congr rfl fun u _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm]

/-- At `T = 0`, `evalVarReplacementRowPoly D e x` evaluates to `bitVal ℚ (x (scopeVarOf scope e))`
(Definition 3.1 (4), p. 22). -/
theorem eval_zero_evalVarReplacementRowPoly {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ)
    (e : ScopeIncidence scope) (x : Fin n → Bool) :
    (evalVarReplacementRowPoly D e x).eval 0 = bitVal ℚ (x (scopeVarOf scope e)) := by
  rw [eval_evalVarReplacementRowPoly, D.evalReplacementRow_zero]

/-- Mapping `evalVarReplacementRowScaledIntPoly D e x` into `ℚ[X]` yields
`C (commonDenom Q R : ℚ) * evalVarReplacementRowPoly D e x` (Definition 3.1 (5) & Lemma 4.6). -/
theorem map_evalVarReplacementRowScaledIntPoly {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ)
    (e : ScopeIncidence scope) (x : Fin n → Bool) :
    (evalVarReplacementRowScaledIntPoly D e x).map (Int.castRingHom ℚ) =
      Polynomial.C (commonDenom Q R : ℚ) * evalVarReplacementRowPoly D e x := by
  rw [evalVarReplacementRowScaledIntPoly, evalVarReplacementRowPoly, Polynomial.map_sum, mul_sum]
  refine sum_congr rfl fun u _ => ?_
  have hbit : (Int.castRingHom ℚ) (bitVal ℤ (x u)) = bitVal ℚ (x u) := by
    cases x u <;> rfl
  rw [Polynomial.map_mul, Polynomial.map_C, hbit, D.map_replacementRowScaledInt e u,
    Algebra.smul_def, algebraMap_eq, mul_left_comm]

/-- At `T = 0`, `evalVarReplacementRowScaledIntPoly D e x` evaluates to
`(commonDenom Q R : ℤ) * bitVal ℤ (x (scopeVarOf scope e))`. -/
theorem eval_zero_evalVarReplacementRowScaledIntPoly {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ)
    (e : ScopeIncidence scope) (x : Fin n → Bool) :
    (evalVarReplacementRowScaledIntPoly D e x).eval 0 =
      (commonDenom Q R : ℤ) * bitVal ℤ (x (scopeVarOf scope e)) := by
  apply Int.cast_injective (α := ℚ)
  have hmap := congrArg (fun p : Polynomial ℚ => p.eval 0)
    (map_evalVarReplacementRowScaledIntPoly D e x)
  rw [Polynomial.eval_mul, Polynomial.eval_C, eval_zero_evalVarReplacementRowPoly] at hmap
  have h0 : (0 : ℚ) = Int.castRingHom ℚ 0 := rfl
  rw [h0, Polynomial.eval_map_apply, eq_intCast] at hmap
  rw [hmap, Int.cast_mul, Int.cast_natCast]
  cases x (scopeVarOf scope e) <;>
    simp only [bitVal_true, bitVal_false, Int.cast_one, Int.cast_zero]

/-- `evalVarReplacementRowPoly D e x` has `natDegree ≤ R - 1` (Definition 3.1 (4)). -/
theorem natDegree_evalVarReplacementRowPoly_le {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ)
    (e : ScopeIncidence scope) (x : Fin n → Bool) :
    (evalVarReplacementRowPoly D e x).natDegree ≤ R - 1 := by
  rw [evalVarReplacementRowPoly]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun u _ => ?_⟩
  exact (Polynomial.natDegree_C_mul_le _ _).trans (D.natDegree_replacementRow_le e u)

/-- `evalVarReplacementRowScaledIntPoly D e x` has `natDegree ≤ R - 1`. -/
theorem natDegree_evalVarReplacementRowScaledIntPoly_le {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ)
    (e : ScopeIncidence scope) (x : Fin n → Bool) :
    (evalVarReplacementRowScaledIntPoly D e x).natDegree ≤ R - 1 := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  rw [← Polynomial.natDegree_map_eq_of_injective hinj, map_evalVarReplacementRowScaledIntPoly]
  exact (Polynomial.natDegree_C_mul_le _ _).trans (natDegree_evalVarReplacementRowPoly_le D e x)

/-- **Lemma 4.6 row `ℓ₁`-norm bound on Boolean inputs**:
`(evalVarReplacementRowScaledIntPoly D e x).coeffNorm1 ≤ designRowNormBound Q R`. -/
theorem coeffNorm1_evalVarReplacementRowScaledIntPoly_le {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ)
    (e : ScopeIncidence scope) (x : Fin n → Bool) :
    (evalVarReplacementRowScaledIntPoly D e x).coeffNorm1 ≤ designRowNormBound Q R := by
  have hsum :
      (evalVarReplacementRowScaledIntPoly D e x).coeffNorm1 ≤
        ∑ u : Fin n,
          (varReplacementRowScaledInt Q r A₀ R D.place (scopeVarOf scope) e u).coeffNorm1 := by
    rw [evalVarReplacementRowScaledIntPoly]
    refine (Polynomial.coeffNorm1_sum_le univ _).trans (sum_le_sum fun u _ => ?_)
    cases x u
    · simp only [bitVal_false, Polynomial.C_0, zero_mul, Polynomial.coeffNorm1_zero, zero_le]
    · simp only [bitVal_true, Polynomial.C_1, one_mul, le_rfl]
  have hrow := D.sum_coeffNorm1_replacementRowScaledInt_le e
  have hrow_nat :
      (∑ u : Fin n,
        (varReplacementRowScaledInt Q r A₀ R D.place (scopeVarOf scope) e u).coeffNorm1) ≤
        designRowNormBound Q R := by
    rw [designRowNormBound]
    exact_mod_cast hrow
  exact hsum.trans hrow_nat

/-- **Definition 3.1 (4) group-and-measurement locality at `nodePoint t`**:
at `t : Fin Q`, `(evalVarReplacementRowPoly D e x).eval (nodePoint t)` depends only on `x`
restricted to `varGroup D.varAssign t (D.factorAssign (scopeFactorOf scope e) t)` and the
measurement vector `(varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec
(fun u => bitVal ℚ (x u))`. -/
theorem eval_evalVarReplacementRowPoly_nodePoint_eq_of_eq_on_varGroup {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ)
    (e : ScopeIncidence scope) (t : Fin Q) (x x' : Fin n → Bool)
    (hgrp : ∀ u ∈ varGroup D.varAssign t (D.factorAssign (scopeFactorOf scope e) t), x u = x' u)
    (hmeas :
      (varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec
          (fun u => bitVal ℚ (x u)) =
        (varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec
          (fun u => bitVal ℚ (x' u))) :
    (evalVarReplacementRowPoly D e x).eval (nodePoint t) =
      (evalVarReplacementRowPoly D e x').eval (nodePoint t) := by
  rw [eval_evalVarReplacementRowPoly, eval_evalVarReplacementRowPoly]
  exact D.evalReplacementRow_nodePoint_eq_of_eq_on_varGroup e t
    (fun u => bitVal ℚ (x u)) (fun u => bitVal ℚ (x' u))
    (fun u hu => congrArg (bitVal ℚ) (hgrp u hu)) hmeas

/-! ### 3. Factor-indexed replacement families `designReplacementMap` and
`designReplacementScaledIntMap` (§5.3–5.4) -/

/-- The equation-indexed rational replacement family `(Fin n → Bool) → κ → Fin n → ℚ[X]` associated
to a `ReplacementDesign` and factor embedding `emb : κ → F`, using
`evalVarReplacementRowPoly D ⟨emb i, ⟨v, hv⟩⟩ x` for `v ∈ scope (emb i)` and the constant Boolean
value `C (bitVal ℚ (x v))` outside `scope (emb i)`. -/
noncomputable def designReplacementMap {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (x : Fin n → Bool) (i : κ) (v : Fin n) : Polynomial ℚ :=
  if hv : v ∈ scope (emb i) then
    evalVarReplacementRowPoly D ⟨emb i, ⟨v, hv⟩⟩ x
  else
    Polynomial.C (bitVal ℚ (x v))

/-- The equation-indexed scaled integer replacement family `(Fin n → Bool) → κ → Fin n → ℤ[X]`
associated to a `ReplacementDesign` and factor embedding `emb : κ → F`, using
`evalVarReplacementRowScaledIntPoly D ⟨emb i, ⟨v, hv⟩⟩ x` for `v ∈ scope (emb i)` and
`C ((commonDenom Q R : ℤ) * bitVal ℤ (x v))` outside `scope (emb i)`. -/
noncomputable def designReplacementScaledIntMap {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (x : Fin n → Bool) (i : κ) (v : Fin n) : Polynomial ℤ :=
  if hv : v ∈ scope (emb i) then
    evalVarReplacementRowScaledIntPoly D ⟨emb i, ⟨v, hv⟩⟩ x
  else
    Polynomial.C ((commonDenom Q R : ℤ) * bitVal ℤ (x v))

/-- On `hv : v ∈ scope (emb i)`, `designReplacementMap D emb x i v` is
`evalVarReplacementRowPoly D ⟨emb i, ⟨v, hv⟩⟩ x`. -/
theorem designReplacementMap_of_mem {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (x : Fin n → Bool) {i : κ} {v : Fin n} (hv : v ∈ scope (emb i)) :
    designReplacementMap D emb x i v = evalVarReplacementRowPoly D ⟨emb i, ⟨v, hv⟩⟩ x := by
  simp only [designReplacementMap, hv, ↓reduceDIte]

/-- On `hv : v ∈ scope (emb i)`, `designReplacementScaledIntMap D emb x i v` is
`evalVarReplacementRowScaledIntPoly D ⟨emb i, ⟨v, hv⟩⟩ x`. -/
theorem designReplacementScaledIntMap_of_mem {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (x : Fin n → Bool) {i : κ} {v : Fin n} (hv : v ∈ scope (emb i)) :
    designReplacementScaledIntMap D emb x i v =
      evalVarReplacementRowScaledIntPoly D ⟨emb i, ⟨v, hv⟩⟩ x := by
  simp only [designReplacementScaledIntMap, hv, ↓reduceDIte]

/-- Mapping `designReplacementScaledIntMap D emb x i v` into `ℚ[X]` yields
`C (commonDenom Q R : ℚ) * designReplacementMap D emb x i v`. -/
theorem map_designReplacementScaledIntMap {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (x : Fin n → Bool) (i : κ) (v : Fin n) :
    (designReplacementScaledIntMap D emb x i v).map (Int.castRingHom ℚ) =
      Polynomial.C (commonDenom Q R : ℚ) * designReplacementMap D emb x i v := by
  unfold designReplacementScaledIntMap designReplacementMap
  split_ifs with hv
  · exact map_evalVarReplacementRowScaledIntPoly D ⟨emb i, ⟨v, hv⟩⟩ x
  · rw [Polynomial.map_C, eq_intCast, Int.cast_mul, Int.cast_natCast, Polynomial.C_mul]
    cases x v <;>
      simp only [bitVal_true, bitVal_false, Int.cast_one, Int.cast_zero, Polynomial.C_1,
        Polynomial.C_0, mul_one, mul_zero]

/-- `divDenomReplacement ℚ (commonDenom Q R : ℤ) (designReplacementScaledIntMap D emb)` agrees
with `designReplacementMap D emb`. -/
theorem divDenomReplacement_designReplacementScaledIntMap {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (x : Fin n → Bool) (i : κ) (v : Fin n) :
    divDenomReplacement ℚ (commonDenom Q R : ℤ) (designReplacementScaledIntMap D emb) x i v =
      designReplacementMap D emb x i v := by
  rw [divDenomReplacement, map_designReplacementScaledIntMap, ← mul_assoc, ← Polynomial.C_mul,
    Int.cast_natCast, inv_mul_cancel₀ (commonDenom_ratCast_ne_zero Q R), Polynomial.C_1, one_mul]

/-- At `T = 0`, `designReplacementMap D emb x i v` evaluates to `bitVal ℚ (x v)`. -/
theorem eval_zero_designReplacementMap {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (x : Fin n → Bool) (i : κ) (v : Fin n) :
    (designReplacementMap D emb x i v).eval 0 = bitVal ℚ (x v) := by
  unfold designReplacementMap
  split_ifs with hv
  · exact eval_zero_evalVarReplacementRowPoly D ⟨emb i, ⟨v, hv⟩⟩ x
  · exact Polynomial.eval_C

/-- At `T = 0`, `designReplacementScaledIntMap D emb x i v` evaluates to
`(commonDenom Q R : ℤ) * bitVal ℤ (x v)`. -/
theorem eval_zero_designReplacementScaledIntMap {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (x : Fin n → Bool) (i : κ) (v : Fin n) :
    (designReplacementScaledIntMap D emb x i v).eval 0 =
      (commonDenom Q R : ℤ) * bitVal ℤ (x v) := by
  unfold designReplacementScaledIntMap
  split_ifs with hv
  · exact eval_zero_evalVarReplacementRowScaledIntPoly D ⟨emb i, ⟨v, hv⟩⟩ x
  · exact Polynomial.eval_C

/-- `designReplacementMap D emb x i v` has `natDegree ≤ R - 1`. -/
theorem natDegree_designReplacementMap_le {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (x : Fin n → Bool) (i : κ) (v : Fin n) :
    (designReplacementMap D emb x i v).natDegree ≤ R - 1 := by
  unfold designReplacementMap
  split_ifs with hv
  · exact natDegree_evalVarReplacementRowPoly_le D ⟨emb i, ⟨v, hv⟩⟩ x
  · rw [Polynomial.natDegree_C]
    exact Nat.zero_le _

/-- `designReplacementScaledIntMap D emb x i v` has `natDegree ≤ R - 1`. -/
theorem natDegree_designReplacementScaledIntMap_le {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (x : Fin n → Bool) (i : κ) (v : Fin n) :
    (designReplacementScaledIntMap D emb x i v).natDegree ≤ R - 1 := by
  unfold designReplacementScaledIntMap
  split_ifs with hv
  · exact natDegree_evalVarReplacementRowScaledIntPoly_le D ⟨emb i, ⟨v, hv⟩⟩ x
  · rw [Polynomial.natDegree_C]
    exact Nat.zero_le _

/-- `(designReplacementScaledIntMap D emb x i v).coeffNorm1 ≤ designRowNormBound Q R`. -/
theorem coeffNorm1_designReplacementScaledIntMap_le {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (x : Fin n → Bool) (i : κ) (v : Fin n) :
    (designReplacementScaledIntMap D emb x i v).coeffNorm1 ≤ designRowNormBound Q R := by
  unfold designReplacementScaledIntMap
  split_ifs with hv
  · exact coeffNorm1_evalVarReplacementRowScaledIntPoly_le D ⟨emb i, ⟨v, hv⟩⟩ x
  · rw [Polynomial.coeffNorm1_C]
    cases x v
    · simp only [bitVal_false, mul_zero, Int.natAbs_zero, zero_le]
    · simp only [bitVal_true, mul_one, Int.natAbs_natCast]
      exact commonDenom_le_designRowNormBound Q R

/-- **Appendix B.2 Stage-1 `ℓ₁`-norm bound for `designReplacementScaledIntMap`**:
if every monomial `M ∈ P i` has `#M ≤ k`, then
`clearedMonomialSumPoly (commonDenom Q R : ℤ) k (designReplacementScaledIntMap D emb x i) (P i)`
has `coeffNorm1 ≤ #(P i) * designRowNormBound Q R ^ k`. -/
theorem coeffNorm1_clearedMonomialSumPoly_designReplacementScaledIntMap_le {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (P : κ → Finset (Finset (Fin n))) (x : Fin n → Bool) {i : κ} {k : ℕ}
    (hk : ∀ M ∈ P i, #M ≤ k) :
    (clearedMonomialSumPoly (commonDenom Q R : ℤ) k
        (designReplacementScaledIntMap D emb x i) (P i)).coeffNorm1 ≤
      #(P i) * designRowNormBound Q R ^ k := by
  refine coeffNorm1_clearedMonomialSumPoly_le ?_ hk
    (fun _ _ v _ => coeffNorm1_designReplacementScaledIntMap_le D emb x i v)
  simpa only [Int.natAbs_natCast] using commonDenom_le_designRowNormBound Q R

/-! ### 4. Concrete §5.3–5.5 degree, homogenization, `ℓ₁`-norm, and exact division recovery
theorems for `ReplacementDesign` -/

/-- **Equation (5.5a) coordinate `natDegree` bound for `ReplacementDesign`**:
for `s < ℓ` and `∀ i ∈ I, ∀ M ∈ P i, #M ≤ k`, the cleared coordinate polynomial
`univariateClearedParityCoord I P (commonDenom Q R : ℤ) k ℓ (designReplacementScaledIntMap D emb) s`
has `natDegree ≤ (k * (R - 1)) * (#I + 2 * (ℓ - 1))`. -/
theorem natDegree_univariateClearedParityCoord_design_le {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) {k ℓ s : ℕ}
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k) (hs : s < ℓ) :
    (univariateClearedParityCoord I P (commonDenom Q R : ℤ) k ℓ
        (designReplacementScaledIntMap D emb) s).natDegree ≤
      (k * (R - 1)) * (#I + 2 * (ℓ - 1)) :=
  natDegree_univariateClearedParityCoord_le I P (commonDenom Q R : ℤ) k ℓ
    (designReplacementScaledIntMap D emb) hk
    (fun x i _ _ _ v _ => natDegree_designReplacementScaledIntMap_le D emb x i v) hs

/-- **Equation (5.5a) truncated-sum `natDegree` bound for `ReplacementDesign`**:
when `∀ i ∈ I, ∀ M ∈ P i, #M ≤ k`, the cleared truncated sum
`univariateClearedParityTruncatedSum I P (commonDenom Q R : ℤ) k ℓ
  (designReplacementScaledIntMap D emb)`
has `natDegree ≤ (k * (R - 1)) * (#I + 2 * (ℓ - 1))`. -/
theorem natDegree_univariateClearedParityTruncatedSum_design_le {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) (k ℓ : ℕ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k) :
    (univariateClearedParityTruncatedSum I P (commonDenom Q R : ℤ) k ℓ
        (designReplacementScaledIntMap D emb)).natDegree ≤
      (k * (R - 1)) * (#I + 2 * (ℓ - 1)) :=
  natDegree_univariateClearedParityTruncatedSum_le I P (commonDenom Q R : ℤ) k ℓ
    (designReplacementScaledIntMap D emb) hk
    (fun x i _ _ _ v _ => natDegree_designReplacementScaledIntMap_le D emb x i v)

/-- **§5.4 & Appendix B.3 ($\tilde{H}_s(T) = \Omega [V^s] H(T)$ over `ℚ[X]` for
`ReplacementDesign`)**: for `1 ≤ ℓ` and `∀ i ∈ I, ∀ M ∈ P i, #M ≤ k`, mapping
`univariateClearedParityCoord I P (commonDenom Q R : ℤ) k ℓ (designReplacementScaledIntMap D emb) s`
into `ℚ[X]` equals `C (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I : ℚ)` times
`univariateParityCoord I P ℓ (designReplacementMap D emb) s`. -/
theorem map_univariateClearedParityCoord_design {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) {k ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k) (s : ℕ) :
    (univariateClearedParityCoord I P (commonDenom Q R : ℤ) k ℓ
        (designReplacementScaledIntMap D emb) s).map (Int.castRingHom ℚ) =
      Polynomial.C (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I : ℚ) *
        univariateParityCoord I P ℓ (designReplacementMap D emb) s :=
  map_univariateClearedParityCoord I P (commonDenom Q R : ℤ) hℓ
    (designReplacementScaledIntMap D emb) (designReplacementMap D emb) hk
    (fun x i _ _ _ v _ => map_designReplacementScaledIntMap D emb x i v) s

/-- **§5.4 & Appendix B.3 ($S_\ell(\tilde{H}(T)) = \Omega S_\ell(H(T))$ over `ℚ[X]` for
`ReplacementDesign`)**: under the same hypotheses, mapping
`univariateClearedParityTruncatedSum I P (commonDenom Q R : ℤ) k ℓ
  (designReplacementScaledIntMap D emb)` into `ℚ[X]` equals
`C (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I : ℚ)` times
`univariateParityTruncatedSum I P ℓ (designReplacementMap D emb)`. -/
theorem map_univariateClearedParityTruncatedSum_design {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) {k ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k) :
    (univariateClearedParityTruncatedSum I P (commonDenom Q R : ℤ) k ℓ
        (designReplacementScaledIntMap D emb)).map (Int.castRingHom ℚ) =
      Polynomial.C (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I : ℚ) *
        univariateParityTruncatedSum I P ℓ (designReplacementMap D emb) :=
  map_univariateClearedParityTruncatedSum I P (commonDenom Q R : ℤ) hℓ
    (designReplacementScaledIntMap D emb) (designReplacementMap D emb) hk
    (fun x i _ _ _ v _ => map_designReplacementScaledIntMap D emb x i v)

/-- **Appendix B.2 coordinate `ℓ₁`-norm bound for `ReplacementDesign`**:
if `∀ i ∈ I, ∀ M ∈ P i, #M ≤ k`, `∀ i ∈ I, #(P i) ≤ S_mon`, and
`∀ j < ℓ, (parityBaseDigit ℓ j).coeffNorm1 ≤ E_ℓ`, then every coordinate polynomial
`univariateClearedParityCoord I P (commonDenom Q R : ℤ) k ℓ (designReplacementScaledIntMap D emb) s`
has `coeffNorm1` at most
`2 ^ n * (ℓ * E_ℓ * (S_mon * designRowNormBound Q R ^ k + commonDenom Q R ^ k) ^ (2 * ℓ - 1)) ^ #I`.
-/
theorem coeffNorm1_univariateClearedParityCoord_design_le {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) (k ℓ : ℕ) {S_mon E_ℓ : ℕ}
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hS : ∀ i ∈ I, #(P i) ≤ S_mon)
    (hE : ∀ j < ℓ, (Polynomial.parityBaseDigit ℓ j).coeffNorm1 ≤ E_ℓ) (s : ℕ) :
    (univariateClearedParityCoord I P (commonDenom Q R : ℤ) k ℓ
        (designReplacementScaledIntMap D emb) s).coeffNorm1 ≤
      2 ^ n *
        (ℓ * E_ℓ *
          (S_mon * designRowNormBound Q R ^ k + commonDenom Q R ^ k) ^ (2 * ℓ - 1)) ^ #I := by
  have hbound :=
    coeffNorm1_univariateClearedParityCoord_le I P (commonDenom Q R : ℤ) k ℓ
      (B := S_mon * designRowNormBound Q R ^ k) (designReplacementScaledIntMap D emb)
      (fun x i hi =>
        (coeffNorm1_clearedMonomialSumPoly_designReplacementScaledIntMap_le D emb P x
          (hk i hi)).trans (Nat.mul_le_mul_right _ (hS i hi)))
      hE s
  simpa only [Fintype.card_fin, ← Int.natCast_pow, Int.natAbs_natCast] using hbound

/-- **§5.4 & Appendix B.3 (exact modular recovery of `commonZeroCount` from coordinate quotients
for `ReplacementDesign`)**: when `n < ℓ` and `∀ i ∈ I, ∀ M ∈ P i, #M ≤ k`, summing the exact
integer quotients
`(univariateClearedParityCoord I P (commonDenom Q R : ℤ) k ℓ
  (designReplacementScaledIntMap D emb) s).eval 0 /
  clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I`
over `s ∈ range ℓ` and reducing modulo `2 ^ ℓ` recovers `commonZeroCount I P`. -/
theorem emod_sum_ediv_eval_zero_clearedParityCoord_design_eq_commonZeroCount
    {F : Type*} [Fintype F] {scope : F → Finset (Fin n)}
    (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) {k ℓ : ℕ} (hℓ : n < ℓ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k) :
    (∑ s ∈ range ℓ,
      (univariateClearedParityCoord I P (commonDenom Q R : ℤ) k ℓ
        (designReplacementScaledIntMap D emb) s).eval 0 /
          clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I) % ((2 : ℤ) ^ ℓ) =
      commonZeroCount I P :=
  emod_sum_ediv_eval_zero_univariateClearedParityCoord_eq_commonZeroCount I P
    (commonDenom_intCast_ne_zero Q R) (by simpa only [Fintype.card_fin] using hℓ)
    (designReplacementScaledIntMap D emb) hk
    (fun x i _ _ _ v _ => eval_zero_designReplacementScaledIntMap D emb x i v)

/-- **§5.4 & Appendix B.3 (exact modular recovery of `commonZeroCount` from
$S_\ell(\tilde{H})(0) / \Omega$ for `ReplacementDesign`)**: under the same hypotheses, dividing
`(univariateClearedParityTruncatedSum I P (commonDenom Q R : ℤ) k ℓ
  (designReplacementScaledIntMap D emb)).eval 0` by
`clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I` and reducing modulo `2 ^ ℓ` recovers
`commonZeroCount I P`. -/
theorem emod_ediv_eval_zero_clearedParityTruncatedSum_design_eq_commonZeroCount
    {F : Type*} [Fintype F] {scope : F → Finset (Fin n)}
    (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) {k ℓ : ℕ} (hℓ : n < ℓ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k) :
    ((univariateClearedParityTruncatedSum I P (commonDenom Q R : ℤ) k ℓ
        (designReplacementScaledIntMap D emb)).eval 0 /
      clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I) % ((2 : ℤ) ^ ℓ) =
      commonZeroCount I P :=
  emod_ediv_eval_zero_univariateClearedParityTruncatedSum_eq_commonZeroCount I P
    (commonDenom_intCast_ne_zero Q R) (by simpa only [Fintype.card_fin] using hℓ)
    (designReplacementScaledIntMap D emb) hk
    (fun x i _ _ _ v _ => eval_zero_designReplacementScaledIntMap D emb x i v)

/-- **Appendix B.3 (eq. B.1, Cramer's rule determinant exact division recovery for
`ReplacementDesign`)**: if `D_H ≠ 0`, `n < ℓ`, `∀ i ∈ I, ∀ M ∈ P i, #M ≤ k`, and
`N_H s = D_H * (univariateClearedParityCoord I P (commonDenom Q R : ℤ) k ℓ
  (designReplacementScaledIntMap D emb) s).eval 0` for all `s ∈ range ℓ`, then summing the exact
integer quotients `N_H s / (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I * D_H)` over
`s ∈ range ℓ` and reducing modulo `2 ^ ℓ` recovers `commonZeroCount I P`. -/
theorem emod_sum_cramer_ediv_design_eq_commonZeroCount {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) {D_H : ℤ} (hDH : D_H ≠ 0)
    {k ℓ : ℕ} (hℓ : n < ℓ) (N_H : ℕ → ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hcramer : ∀ s ∈ range ℓ,
      N_H s = D_H * (univariateClearedParityCoord I P (commonDenom Q R : ℤ) k ℓ
        (designReplacementScaledIntMap D emb) s).eval 0) :
    (∑ s ∈ range ℓ,
      N_H s / (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I * D_H)) % ((2 : ℤ) ^ ℓ) =
      commonZeroCount I P :=
  emod_sum_cramer_ediv_eq_commonZeroCount I P (commonDenom_intCast_ne_zero Q R) hDH
    (by simpa only [Fintype.card_fin] using hℓ) (designReplacementScaledIntMap D emb) N_H hk
    (fun x i _ _ _ v _ => eval_zero_designReplacementScaledIntMap D emb x i v) hcramer

/-- **§5.5 & Appendix B.3 (branch-summed exact integer division recovery from per-branch
`ReplacementDesign`s at shared precision $\ell = n + 1$)**: given a heavy-variable subset
`S : Finset (Fin n)`, a relabeling `e : ↥(univ \ S) ≃ Fin n'` of the free variables, and a
per-branch `ReplacementDesign` family `D : (Fin n → Bool) → ReplacementDesign (scope b) Q r A₀ R τ`
(with factor embeddings `emb b : κ → F`), summing the branch modular residues at shared precision
`branchPrecision n = n + 1` across `b ∈ branchAssignments S` recovers `commonZeroCount I P`. -/
theorem commonZeroCount_eq_sum_branch_emod_ediv_design {F : Type*} [Fintype F] {n' : ℕ}
    (S : Finset (Fin n)) (e : ↥(univ \ S) ≃ Fin n')
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) {k : ℕ}
    (scope : (Fin n → Bool) → F → Finset (Fin n'))
    (D : (b : Fin n → Bool) → ReplacementDesign (scope b) Q r A₀ R τ)
    (emb : (Fin n → Bool) → κ → F)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k) :
    (commonZeroCount I P : ℤ) =
      ∑ b ∈ branchAssignments S,
        ((univariateClearedParityTruncatedSum I
          (fun i => relabelRestrictedMonomials S e b (P i))
          (commonDenom Q R : ℤ) k (branchPrecision n)
          (designReplacementScaledIntMap (D b) (emb b))).eval 0 /
            clearedProductDenom (commonDenom Q R : ℤ) k (branchPrecision n) #I) %
              ((2 : ℤ) ^ branchPrecision n) := by
  simpa only [Fintype.card_fin] using
    commonZeroCount_eq_sum_branch_emod_ediv_cleared S e I P
      (commonDenom_intCast_ne_zero Q R)
      (fun b => designReplacementScaledIntMap (D b) (emb b)) hk
      (fun b _ x i _ _ _ v _ => eval_zero_designReplacementScaledIntMap (D b) (emb b) x i v)

end Cslib.BitString
