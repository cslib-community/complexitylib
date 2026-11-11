/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxCut.GoemansWilliamson
public import CslibFrontier.Logics.Propositional.CNF
import CslibFrontier.Foundations.Analysis.Normed.UnitSphere

/-!
# Goemans–Williamson random-hyperplane rounding for MAX-2SAT

This module formalizes the MAX-2SAT extension of Goemans–Williamson random-hyperplane rounding
[GoemansWilliamson1995, Section 7.2.1], reusing the MAX-CUT constant
`Real.goemansWilliamsonConstant` (`α > 0.87856`) and Gaussian expectation analysis from
`CslibFrontier.Algorithms.Lean.MaxCut.GoemansWilliamson`.

## Main definitions

* `Cslib.Algorithms.Lean.MaxTwoSAT.signedCutValue`,
  `Cslib.Algorithms.Lean.MaxTwoSAT.signedSdpValue`: the signed-pair quadratic program `(Q')` and
  its semidefinite relaxation `(P')` (normalized by `1 / 2` to match MAX-CUT's `sdpValue`).
* `Cslib.Algorithms.Lean.MaxTwoSAT.litVector`,
  `Cslib.Algorithms.Lean.MaxTwoSAT.satSdpClause`: the homogeneous vector relaxation of a literal
  and a clause of length at most `2` using a distinguished truth-anchor vertex `none : Option V`.
* `Cslib.Algorithms.Lean.MaxTwoSAT.satValue`,
  `Cslib.Algorithms.Lean.MaxTwoSAT.satSdpValue`: weighted satisfied-clause objective and its
  relaxation.
* `Cslib.Algorithms.Lean.MaxTwoSAT.satHyperplaneAssignment`: the Boolean assignment induced by
  random-hyperplane rounding
  (`x` is true iff `hyperplaneSide v r (some x) = hyperplaneSide v r none`).

## Main results

* `goemansWilliamsonConstant_mul_signedSdpValue_le_integral`: Theorem 7.2.1.1 of
  [GoemansWilliamson1995] for `(P')`, plus `ε`-optimal guarantees for `(Q')`.
* `goemansWilliamsonConstant_mul_satSdpValue_le_integral`,
  `goemansWilliamsonConstant_mul_sub_le_integral`: for any weighted collection of clauses of length
  at most `2`, `ε`-optimal unit vectors give expected weight at least `α (satValue σ - ε)`.
* `exists_forall_goemansWilliamsonConstant_mul_sub_le`, `exists_isMaxOn_satSdpValue`.

## Limitations

As with `CslibFrontier.Algorithms.Lean.MaxCut.GoemansWilliamson`, this analyzes rounding of a given
vector solution under Mathlib's exact `stdGaussian`; polynomial-time SDP solving, finite-precision
sampling, and the MAX-SAT LP/SDP hybrid algorithm ([GoemansWilliamson1995, Section 7.2.2]) are
not formalized.

## References

* [GoemansWilliamson1995]
-/

public section

open MeasureTheory ProbabilityTheory Real Set Cslib.Logic.PL
open scoped RealInnerProductSpace

namespace Cslib.Algorithms.Lean.MaxTwoSAT

open Cslib.Algorithms.Lean.MaxCut

variable {ι V F : Type*} [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### Signed-pair quadratic program `(Q')` and relaxation `(P')` -/

/-- Objective of the generalized quadratic program `(Q')` [GoemansWilliamson1995, Section 7.2.1],
normalized by `1 / 2` to match `cutValue`: `a e` pays when endpoints lie on opposite sides and
`b e` pays when endpoints lie on the same side. -/
@[expose] noncomputable def signedCutValue (ends : ι → V × V) (a b : ι → ℝ) (side : V → Bool) :
    ℝ :=
  ∑ e, ((if side (ends e).1 ≠ side (ends e).2 then a e else 0) +
    (if side (ends e).1 = side (ends e).2 then b e else 0))

/-- Objective of the semidefinite relaxation `(P')` [GoemansWilliamson1995, Section 7.2.1],
normalized by `1 / 2`: `∑ e, (a e * (1 - ⟪v i, v j⟫) / 2 + b e * (1 + ⟪v i, v j⟫) / 2)`. -/
@[expose] noncomputable def signedSdpValue (ends : ι → V × V) (a b : ι → ℝ) (v : V → F) : ℝ :=
  ∑ e, (a e * (1 - ⟪v (ends e).1, v (ends e).2⟫) / 2 +
    b e * (1 + ⟪v (ends e).1, v (ends e).2⟫) / 2)

/-- At a cut's `±u` vector solution, `signedSdpValue` equals `signedCutValue`. -/
theorem signedSdpValue_signVector (ends : ι → V × V) (a b : ι → ℝ) {u : F} (hu : ‖u‖ = 1)
    (side : V → Bool) :
    signedSdpValue ends a b (signVector u side) = signedCutValue ends a b side := by
  unfold signedSdpValue signedCutValue
  refine Finset.sum_congr rfl fun e _ => ?_
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  unfold signVector
  cases side (ends e).1 <;> cases side (ends e).2 <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, ne_eq, not_true_eq_false,
      not_false_eq_true, inner_neg_left, inner_neg_right, neg_neg, huu] <;> ring

/-- If unit vectors `v` are within `ε` of optimal for `signedSdpValue`, then every Boolean cut has
value at most `signedSdpValue ends a b v + ε`. -/
theorem signedCutValue_le_signedSdpValue_add {ends : ι → V × V} {a b : ι → ℝ} {v : V → F} {ε : ℝ}
    (hv : ∀ i, ‖v i‖ = 1)
    (hopt : ∀ v' : V → F, (∀ i, ‖v' i‖ = 1) →
      signedSdpValue ends a b v' ≤ signedSdpValue ends a b v + ε)
    (side : V → Bool) : signedCutValue ends a b side ≤ signedSdpValue ends a b v + ε := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    have := hopt v hv
    simp only [signedCutValue, signedSdpValue, Finset.univ_eq_empty, Finset.sum_empty] at this ⊢
    exact this
  | inr h =>
    obtain ⟨e⟩ := h
    rw [← signedSdpValue_signVector ends a b (hv (ends e).1) side]
    exact hopt _ (norm_signVector (hv (ends e).1) side)

section SignedMeasurable

variable [MeasurableSpace F] [BorelSpace F]

/-- `signedCutValue` along a random hyperplane is integrable under any finite measure. -/
theorem integrable_signedCutValue_hyperplaneSide (ends : ι → V × V) (a b : ι → ℝ) (v : V → F)
    (μ : Measure F) [IsFiniteMeasure μ] :
    Integrable (fun r => signedCutValue ends a b (hyperplaneSide v r)) μ := by
  unfold signedCutValue
  exact integrable_finsetSum _ fun e _ =>
    (integrable_ite_const μ (measurableSet_hyperplaneSide_ne v (ends e).1 (ends e).2) (a e)).add
      (integrable_ite_const μ (measurableSet_hyperplaneSide_eq v (ends e).1 (ends e).2) (b e))

variable [FiniteDimensional ℝ F]

/-- Expected `signedCutValue` under random-hyperplane rounding. -/
theorem integral_signedCutValue_hyperplaneSide (ends : ι → V × V) (a b : ι → ℝ) {v : V → F}
    (hv : ∀ i, ‖v i‖ = 1) :
    ∫ r, signedCutValue ends a b (hyperplaneSide v r) ∂stdGaussian F =
      ∑ e, (a e * (arccos ⟪v (ends e).1, v (ends e).2⟫ / π) +
        b e * (1 - arccos ⟪v (ends e).1, v (ends e).2⟫ / π)) := by
  unfold signedCutValue
  have hint : ∀ e ∈ (Finset.univ : Finset ι), Integrable (fun r : F =>
      (if hyperplaneSide v r (ends e).1 ≠ hyperplaneSide v r (ends e).2 then a e else 0) +
        if hyperplaneSide v r (ends e).1 = hyperplaneSide v r (ends e).2 then b e else 0)
      (stdGaussian F) := fun e _ =>
    (integrable_ite_const _ (measurableSet_hyperplaneSide_ne v (ends e).1 (ends e).2) (a e)).add
      (integrable_ite_const _ (measurableSet_hyperplaneSide_eq v (ends e).1 (ends e).2) (b e))
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_add
    (integrable_ite_const _ (measurableSet_hyperplaneSide_ne v (ends e).1 (ends e).2) (a e))
    (integrable_ite_const _ (measurableSet_hyperplaneSide_eq v (ends e).1 (ends e).2) (b e))]
  have hmul1 : (fun r : F =>
      if hyperplaneSide v r (ends e).1 ≠ hyperplaneSide v r (ends e).2 then a e else 0) =
      fun r : F => a e *
        (if hyperplaneSide v r (ends e).1 ≠ hyperplaneSide v r (ends e).2 then (1 : ℝ) else 0) := by
    ext r; split_ifs <;> ring
  have hmul2 : (fun r : F =>
      if hyperplaneSide v r (ends e).1 = hyperplaneSide v r (ends e).2 then b e else 0) =
      fun r : F => b e *
        (if hyperplaneSide v r (ends e).1 = hyperplaneSide v r (ends e).2 then (1 : ℝ) else 0) := by
    ext r; split_ifs <;> ring
  rw [hmul1, hmul2, integral_const_mul, integral_const_mul,
    integral_hyperplaneSide_ne hv, integral_hyperplaneSide_eq hv]

/-- **Goemans–Williamson, Theorem 7.2.1.1.** For nonnegative weights `a` and `b` and unit vectors
`v`, the expected `signedCutValue` under random-hyperplane rounding is at least
`α * signedSdpValue ends a b v` [GoemansWilliamson1995, Theorem 7.2.1.1]. -/
theorem goemansWilliamsonConstant_mul_signedSdpValue_le_integral (ends : ι → V × V)
    {a b : ι → ℝ} (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e) {v : V → F} (hv : ∀ i, ‖v i‖ = 1) :
    goemansWilliamsonConstant * signedSdpValue ends a b v ≤
      ∫ r, signedCutValue ends a b (hyperplaneSide v r) ∂stdGaussian F := by
  rw [integral_signedCutValue_hyperplaneSide ends a b hv, signedSdpValue, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  have h := abs_real_inner_le_norm (v (ends e).1) (v (ends e).2)
  rw [hv, hv, mul_one, abs_le] at h
  have h1 := mul_le_mul_of_nonneg_left (goemansWilliamsonConstant_mul_le_arccos h.1 h.2) (ha e)
  have h2 := mul_le_mul_of_nonneg_left
    (goemansWilliamsonConstant_mul_one_add_le_one_sub_arccos (hv (ends e).1) (hv (ends e).2)) (hb e)
  linarith

/-- The `ε`-optimal guarantee for `(Q')`: `α * (signedCutValue side - ε) ≤ E[signedCutValue]`. -/
theorem goemansWilliamsonConstant_mul_signedCutValue_sub_le_integral (ends : ι → V × V)
    {a b : ι → ℝ} (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e) {v : V → F} (hv : ∀ i, ‖v i‖ = 1)
    {ε : ℝ} (hopt : ∀ v' : V → F, (∀ i, ‖v' i‖ = 1) →
      signedSdpValue ends a b v' ≤ signedSdpValue ends a b v + ε)
    (side : V → Bool) :
    goemansWilliamsonConstant * (signedCutValue ends a b side - ε) ≤
      ∫ r, signedCutValue ends a b (hyperplaneSide v r) ∂stdGaussian F :=
  (mul_le_mul_of_nonneg_left (by linarith [signedCutValue_le_signedSdpValue_add hv hopt side])
    goemansWilliamsonConstant_nonneg).trans
    (goemansWilliamsonConstant_mul_signedSdpValue_le_integral ends ha hb hv)

/-- Exact-optimum guarantee for `(Q')`. -/
theorem goemansWilliamsonConstant_mul_signedCutValue_le_integral (ends : ι → V × V)
    {a b : ι → ℝ} (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e) {v : V → F} (hv : ∀ i, ‖v i‖ = 1)
    (hopt : IsMaxOn (signedSdpValue ends a b) {v' | ∀ i, ‖v' i‖ = 1} v) (side : V → Bool) :
    goemansWilliamsonConstant * signedCutValue ends a b side ≤
      ∫ r, signedCutValue ends a b (hyperplaneSide v r) ∂stdGaussian F := by
  simpa only [sub_zero] using goemansWilliamsonConstant_mul_signedCutValue_sub_le_integral
    ends ha hb hv (ε := 0)
    (fun v' hv' => (add_zero (signedSdpValue ends a b v)).symm ▸ isMaxOn_iff.1 hopt v' hv') side

/-- Some hyperplane realizes the `(Q')` guarantee simultaneously against every cut. -/
theorem exists_forall_goemansWilliamsonConstant_mul_signedCutValue_sub_le (ends : ι → V × V)
    {a b : ι → ℝ} (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e) {v : V → F} (hv : ∀ i, ‖v i‖ = 1)
    {ε : ℝ} (hopt : ∀ v' : V → F, (∀ i, ‖v' i‖ = 1) →
      signedSdpValue ends a b v' ≤ signedSdpValue ends a b v + ε) :
    ∃ r : F, ∀ side : V → Bool,
      goemansWilliamsonConstant * (signedCutValue ends a b side - ε) ≤
        signedCutValue ends a b (hyperplaneSide v r) := by
  obtain ⟨r, hr⟩ := exists_integral_le
    (integrable_signedCutValue_hyperplaneSide ends a b v (stdGaussian F))
  exact ⟨r, fun side =>
    (goemansWilliamsonConstant_mul_signedCutValue_sub_le_integral ends ha hb hv hopt side).trans hr⟩

end SignedMeasurable

/-- Optimal unit vectors exist for `signedSdpValue` in every nontrivial finite-dimensional `F`. -/
theorem exists_isMaxOn_signedSdpValue [FiniteDimensional ℝ F] [Nontrivial F]
    (ends : ι → V × V) (a b : ι → ℝ) :
    ∃ v : V → F, (∀ i, ‖v i‖ = 1) ∧ IsMaxOn (signedSdpValue ends a b) {v' | ∀ i, ‖v' i‖ = 1} v :=
  NormedSpace.exists_isMaxOn_unitSphereFun (by unfold signedSdpValue; fun_prop)

/-! ### Boolean MAX-2SAT relaxation and random-hyperplane rounding -/

/-- The signed vector of a literal `ℓ` under `v : Option V → F`: `v (some x)` for a positive
literal `x` and `-v (some x)` for a negated literal `¬x`. -/
@[expose] noncomputable def litVector (v : Option V → F) (ℓ : Literal V) : F :=
  if ℓ.2 then v (some ℓ.1) else -v (some ℓ.1)

omit [Fintype ι] [InnerProductSpace ℝ F] in
/-- `litVector` has norm `1` when all vectors of `v` do. -/
theorem norm_litVector {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1) (ℓ : Literal V) :
    ‖litVector v ℓ‖ = 1 := by
  unfold litVector
  split <;> simp [hv]

/-- The semidefinite relaxation value of a clause of length at most `2`
[GoemansWilliamson1995, Section 7.2.1], using `none : Option V` as the truth-anchor `v₀`:
- `[]` has value `0`
- `[ℓ]` has value `(1 + ⟪litVector v ℓ, v none⟫) / 2`
- `[ℓ₁, ℓ₂]` has value
  `(1 + ⟪litVector v ℓ₁, v none⟫) / 4 + (1 + ⟪litVector v ℓ₂, v none⟫) / 4 +
    (1 - ⟪litVector v ℓ₁, litVector v ℓ₂⟫) / 4`. -/
@[expose] noncomputable def satSdpClause (v : Option V → F) : Clause V → ℝ
  | [] => 0
  | [ℓ] => (1 + ⟪litVector v ℓ, v none⟫) / 2
  | ℓ₁ :: ℓ₂ :: _ =>
      (1 + ⟪litVector v ℓ₁, v none⟫) / 4 + (1 + ⟪litVector v ℓ₂, v none⟫) / 4 +
        (1 - ⟪litVector v ℓ₁, litVector v ℓ₂⟫) / 4

/-- Total weight of clauses in `clauses` satisfied by the Boolean assignment `σ`. -/
@[expose] noncomputable def satValue (clauses : ι → Clause V) (w : ι → ℝ) (σ : V → Bool) : ℝ :=
  ∑ j, if (clauses j).eval σ then w j else 0

/-- Semidefinite relaxation objective of weighted MAX-2SAT at vector assignment
`v : Option V → F`. -/
@[expose] noncomputable def satSdpValue (clauses : ι → Clause V) (w : ι → ℝ)
    (v : Option V → F) : ℝ :=
  ∑ j, w j * satSdpClause v (clauses j)

/-- Boolean assignment decoded from a partition `side : Option V → Bool`: variable `x` is `true`
iff `side (some x) = side none` [GoemansWilliamson1995, Section 7.2.1]. -/
@[expose] def truthAssignment (side : Option V → Bool) (x : V) : Bool :=
  side (some x) == side none

/-- Boolean assignment induced by random-hyperplane rounding at `r : F`. -/
@[expose] noncomputable def satHyperplaneAssignment (v : Option V → F) (r : F) : V → Bool :=
  truthAssignment (hyperplaneSide v r)

/-- Homogeneous `±u` vector lift of a Boolean assignment `σ : V → Bool` (sending anchor `none` to
`u` and `some x` to `u` if `σ x` else `-u`). -/
@[expose] def liftAssignment (u : F) (σ : V → Bool) : Option V → F :=
  signVector u fun o => o.elim true σ

omit [Fintype ι] in
private theorem satSdpClause_signVector {u : F} (hu : ‖u‖ = 1) (side : Option V → Bool)
    {c : Clause V} (hc : c.length ≤ 2) :
    satSdpClause (signVector u side) c = if c.eval (truthAssignment side) then 1 else 0 := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hlit : ∀ ℓ : Literal V,
      (1 + ⟪litVector (signVector u side) ℓ, signVector u side none⟫) / 2 =
        if ℓ.eval (truthAssignment side) then 1 else 0 := by
    intro ⟨x, p⟩
    unfold litVector Literal.eval truthAssignment signVector
    cases p <;> cases side (some x) <;> cases side none <;>
      simp [inner_neg_left, inner_neg_right, hu]
  have hpair : ∀ ℓ₁ ℓ₂ : Literal V,
      (1 - ⟪litVector (signVector u side) ℓ₁, litVector (signVector u side) ℓ₂⟫) / 2 =
        if ℓ₁.eval (truthAssignment side) ≠ ℓ₂.eval (truthAssignment side) then 1 else 0 := by
    intro ⟨x₁, p₁⟩ ⟨x₂, p₂⟩
    unfold litVector Literal.eval truthAssignment signVector
    cases p₁ <;> cases p₂ <;> cases side (some x₁) <;> cases side (some x₂) <;>
      cases side none <;> simp [inner_neg_left, inner_neg_right, hu]
  rcases c with _ | ⟨ℓ₁, _ | ⟨ℓ₂, _ | ⟨ℓ₃, t⟩⟩⟩
  · simp [satSdpClause]
  · simpa [satSdpClause] using hlit ℓ₁
  · have h1 := hlit ℓ₁
    have h2 := hlit ℓ₂
    have hp := hpair ℓ₁ ℓ₂
    simp only [satSdpClause, Clause.eval_cons, Clause.eval_nil, Bool.or_false]
    have hbool : ∀ b₁ b₂ : Bool,
        (if (b₁ || b₂) = true then (1 : ℝ) else 0) =
          ((if b₁ = true then 1 else 0) + (if b₂ = true then 1 else 0) +
            (if b₁ ≠ b₂ then 1 else 0)) / 2 := by
      intro b₁ b₂; cases b₁ <;> cases b₂ <;> norm_num
    rw [hbool (ℓ₁.eval (truthAssignment side)) (ℓ₂.eval (truthAssignment side))]
    linarith
  · simp at hc

/-- At `liftAssignment u σ` (for `‖u‖ = 1`), `satSdpValue` equals `satValue`. -/
theorem satSdpValue_liftAssignment (clauses : ι → Clause V)
    (hc : ∀ j, (clauses j).length ≤ 2) (w : ι → ℝ) {u : F} (hu : ‖u‖ = 1) (σ : V → Bool) :
    satSdpValue clauses w (liftAssignment u σ) = satValue clauses w σ := by
  unfold satSdpValue satValue liftAssignment
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [satSdpClause_signVector hu _ (hc j)]
  have htr : truthAssignment (fun o : Option V => o.elim true σ) = σ := by
    ext x; simp [truthAssignment]
  rw [htr]
  split_ifs <;> ring

/-- `ε`-optimal unit vectors for `satSdpValue` beat every Boolean assignment up to `ε`. -/
theorem satValue_le_satSdpValue_add {clauses : ι → Clause V} (hc : ∀ j, (clauses j).length ≤ 2)
    {w : ι → ℝ} {v : Option V → F} {ε : ℝ} (hv : ∀ o, ‖v o‖ = 1)
    (hopt : ∀ v' : Option V → F, (∀ o, ‖v' o‖ = 1) →
      satSdpValue clauses w v' ≤ satSdpValue clauses w v + ε)
    (σ : V → Bool) : satValue clauses w σ ≤ satSdpValue clauses w v + ε := by
  rw [← satSdpValue_liftAssignment clauses hc w (hv none) σ]
  exact hopt _ (norm_signVector (hv none) _)

section SatMeasurable

variable [MeasurableSpace F] [BorelSpace F]

private theorem measurableSet_literal_eval (v : Option V → F) (ℓ : Literal V) :
    MeasurableSet {r : F | ℓ.eval (satHyperplaneAssignment v r) = true} := by
  rcases ℓ with ⟨x, b⟩
  cases b
  · have heq : {r : F | Literal.eval (satHyperplaneAssignment v r) (x, false) = true} =
        {r : F | hyperplaneSide v r (some x) ≠ hyperplaneSide v r none} := by
      ext r
      cases h1 : hyperplaneSide v r (some x) <;> cases h0 : hyperplaneSide v r none <;>
        simp [Literal.eval, satHyperplaneAssignment, truthAssignment, h1, h0]
    rw [heq]
    exact measurableSet_hyperplaneSide_ne v (some x) none
  · have heq : {r : F | Literal.eval (satHyperplaneAssignment v r) (x, true) = true} =
        {r : F | hyperplaneSide v r (some x) = hyperplaneSide v r none} := by
      ext r
      cases h1 : hyperplaneSide v r (some x) <;> cases h0 : hyperplaneSide v r none <;>
        simp [Literal.eval, satHyperplaneAssignment, truthAssignment, h1, h0]
    rw [heq]
    exact measurableSet_hyperplaneSide_eq v (some x) none

private theorem measurableSet_clause_eval (v : Option V → F) (c : Clause V) :
    MeasurableSet {r : F | c.eval (satHyperplaneAssignment v r) = true} := by
  induction c with
  | nil => simp [Clause.eval]
  | cons ℓ t ih =>
    simpa only [Clause.eval_cons, Bool.or_eq_true, Set.ofPred_or] using
      (measurableSet_literal_eval v ℓ).union ih

/-- The weighted satisfied-clause value under random-hyperplane rounding is integrable. -/
theorem integrable_satValue_satHyperplaneAssignment (clauses : ι → Clause V) (w : ι → ℝ)
    (v : Option V → F) (μ : Measure F) [IsFiniteMeasure μ] :
    Integrable (fun r => satValue clauses w (satHyperplaneAssignment v r)) μ := by
  unfold satValue
  exact integrable_finsetSum _ fun j _ =>
    integrable_ite_const μ (measurableSet_clause_eval v (clauses j)) (w j)

variable [FiniteDimensional ℝ F]

private theorem integral_literal_eval {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1) (ℓ : Literal V) :
    ∫ r : F, (if ℓ.eval (satHyperplaneAssignment v r) then (1 : ℝ) else 0) ∂stdGaussian F =
      1 - arccos ⟪litVector v ℓ, v none⟫ / π := by
  rcases ℓ with ⟨x, b⟩
  cases b
  · have hev : (fun r : F =>
        if Literal.eval (satHyperplaneAssignment v r) (x, false) then (1 : ℝ) else 0) =
        fun r : F =>
          if hyperplaneSide v r (some x) ≠ hyperplaneSide v r none then (1 : ℝ) else 0 := by
      ext r
      simp [Literal.eval, satHyperplaneAssignment, truthAssignment]
    rw [hev, integral_hyperplaneSide_ne hv (some x) none, litVector]
    simp [inner_neg_left, arccos_neg, sub_div]
  · have hev : (fun r : F =>
        if Literal.eval (satHyperplaneAssignment v r) (x, true) then (1 : ℝ) else 0) =
        fun r : F =>
          if hyperplaneSide v r (some x) = hyperplaneSide v r none then (1 : ℝ) else 0 := by
      ext r
      simp [Literal.eval, satHyperplaneAssignment, truthAssignment]
    rw [hev, integral_hyperplaneSide_eq hv (some x) none, litVector]
    simp

private theorem integral_literal_eval_ne {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1)
    (ℓ₁ ℓ₂ : Literal V) :
    ∫ r : F, (if ℓ₁.eval (satHyperplaneAssignment v r) ≠ ℓ₂.eval (satHyperplaneAssignment v r)
      then (1 : ℝ) else 0) ∂stdGaussian F =
      arccos ⟪litVector v ℓ₁, litVector v ℓ₂⟫ / π := by
  rcases ℓ₁ with ⟨x₁, b₁⟩
  rcases ℓ₂ with ⟨x₂, b₂⟩
  by_cases hb : b₁ = b₂
  · subst hb
    have hev : (fun r : F =>
        if Literal.eval (satHyperplaneAssignment v r) (x₁, b₁) ≠
            Literal.eval (satHyperplaneAssignment v r) (x₂, b₁) then (1 : ℝ) else 0) =
        fun r : F =>
          if hyperplaneSide v r (some x₁) ≠ hyperplaneSide v r (some x₂) then (1 : ℝ) else 0 := by
      ext r
      cases b₁ <;> cases h1 : hyperplaneSide v r (some x₁) <;>
        cases h2 : hyperplaneSide v r (some x₂) <;> cases h0 : hyperplaneSide v r none <;>
        simp [Literal.eval, satHyperplaneAssignment, truthAssignment, h1, h2, h0]
    rw [hev, integral_hyperplaneSide_ne hv (some x₁) (some x₂), litVector, litVector]
    cases b₁ <;> simp
  · have hev : (fun r : F =>
        if Literal.eval (satHyperplaneAssignment v r) (x₁, b₁) ≠
            Literal.eval (satHyperplaneAssignment v r) (x₂, b₂) then (1 : ℝ) else 0) =
        fun r : F =>
          if hyperplaneSide v r (some x₁) = hyperplaneSide v r (some x₂) then (1 : ℝ) else 0 := by
      ext r
      cases b₁ <;> cases b₂
      · exact absurd rfl hb
      · cases h1 : hyperplaneSide v r (some x₁) <;> cases h2 : hyperplaneSide v r (some x₂) <;>
          cases h0 : hyperplaneSide v r none <;>
          simp [Literal.eval, satHyperplaneAssignment, truthAssignment, h1, h2, h0]
      · cases h1 : hyperplaneSide v r (some x₁) <;> cases h2 : hyperplaneSide v r (some x₂) <;>
          cases h0 : hyperplaneSide v r none <;>
          simp [Literal.eval, satHyperplaneAssignment, truthAssignment, h1, h2, h0]
      · exact absurd rfl hb
    rw [hev, integral_hyperplaneSide_eq hv (some x₁) (some x₂), litVector, litVector]
    cases b₁ <;> cases b₂
    · exact absurd rfl hb
    · simp [inner_neg_left, arccos_neg, sub_div]
    · simp [inner_neg_right, arccos_neg, sub_div]
    · exact absurd rfl hb

private theorem goemansWilliamsonConstant_mul_satSdpClause_le_integral {v : Option V → F}
    (hv : ∀ o, ‖v o‖ = 1) {c : Clause V} (hc : c.length ≤ 2) :
    goemansWilliamsonConstant * satSdpClause v c ≤
      ∫ r : F, (if c.eval (satHyperplaneAssignment v r) then (1 : ℝ) else 0) ∂stdGaussian F := by
  rcases c with _ | ⟨ℓ₁, _ | ⟨ℓ₂, _ | ⟨ℓ₃, t⟩⟩⟩
  · simp [satSdpClause, Clause.eval]
  · simp only [satSdpClause, Clause.eval_cons, Clause.eval_nil, Bool.or_false]
    rw [integral_literal_eval hv ℓ₁]
    exact goemansWilliamsonConstant_mul_one_add_le_one_sub_arccos (norm_litVector hv ℓ₁) (hv none)
  · have hi1 : Integrable (fun r : F =>
        if ℓ₁.eval (satHyperplaneAssignment v r) = true then (1 : ℝ) else 0) (stdGaussian F) :=
      integrable_ite_const (stdGaussian F) (measurableSet_literal_eval v ℓ₁) 1
    have hi2 : Integrable (fun r : F =>
        if ℓ₂.eval (satHyperplaneAssignment v r) = true then (1 : ℝ) else 0) (stdGaussian F) :=
      integrable_ite_const (stdGaussian F) (measurableSet_literal_eval v ℓ₂) 1
    have hne_set : MeasurableSet {r : F | ℓ₁.eval (satHyperplaneAssignment v r) ≠
        ℓ₂.eval (satHyperplaneAssignment v r)} := by
      have hm : {r : F | ℓ₁.eval (satHyperplaneAssignment v r) ≠
          ℓ₂.eval (satHyperplaneAssignment v r)} =
          ({r | ℓ₁.eval (satHyperplaneAssignment v r) = true} \
            {r | ℓ₂.eval (satHyperplaneAssignment v r) = true}) ∪
          ({r | ℓ₂.eval (satHyperplaneAssignment v r) = true} \
            {r | ℓ₁.eval (satHyperplaneAssignment v r) = true}) := by
        ext r
        rcases h1 : ℓ₁.eval (satHyperplaneAssignment v r) with _ | _ <;>
          rcases h2 : ℓ₂.eval (satHyperplaneAssignment v r) with _ | _ <;>
          simp only [Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq, ne_eq, h1, h2,
            Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false,
            and_self, and_true, and_false, or_self, or_false, false_or]
      rw [hm]
      exact ((measurableSet_literal_eval v ℓ₁).diff (measurableSet_literal_eval v ℓ₂)).union
        ((measurableSet_literal_eval v ℓ₂).diff (measurableSet_literal_eval v ℓ₁))
    have hip : Integrable (fun r : F =>
        if ℓ₁.eval (satHyperplaneAssignment v r) ≠ ℓ₂.eval (satHyperplaneAssignment v r)
          then (1 : ℝ) else 0) (stdGaussian F) :=
      integrable_ite_const (stdGaussian F) hne_set 1
    have hi12 : Integrable (fun r : F =>
        (if ℓ₁.eval (satHyperplaneAssignment v r) = true then (1 : ℝ) else 0) +
          (if ℓ₂.eval (satHyperplaneAssignment v r) = true then 1 else 0)) (stdGaussian F) :=
      hi1.add hi2
    have hsplit : (fun r : F =>
        if Clause.eval (satHyperplaneAssignment v r) [ℓ₁, ℓ₂] then (1 : ℝ) else 0) =
        fun r : F =>
          ((if ℓ₁.eval (satHyperplaneAssignment v r) = true then (1 : ℝ) else 0) +
            (if ℓ₂.eval (satHyperplaneAssignment v r) = true then 1 else 0) +
            (if ℓ₁.eval (satHyperplaneAssignment v r) ≠ ℓ₂.eval (satHyperplaneAssignment v r)
              then 1 else 0)) / 2 := by
      ext r
      simp only [Clause.eval_cons, Clause.eval_nil, Bool.or_false]
      cases ℓ₁.eval (satHyperplaneAssignment v r) <;>
        cases ℓ₂.eval (satHyperplaneAssignment v r) <;> norm_num
    rw [hsplit, integral_div, integral_add hi12 hip, integral_add hi1 hi2,
      integral_literal_eval hv ℓ₁, integral_literal_eval hv ℓ₂, integral_literal_eval_ne hv ℓ₁ ℓ₂]
    have hgw1 := goemansWilliamsonConstant_mul_one_add_le_one_sub_arccos
      (norm_litVector hv ℓ₁) (hv none)
    have hgw2 := goemansWilliamsonConstant_mul_one_add_le_one_sub_arccos
      (norm_litVector hv ℓ₂) (hv none)
    have hinner := abs_real_inner_le_norm (litVector v ℓ₁) (litVector v ℓ₂)
    rw [norm_litVector hv ℓ₁, norm_litVector hv ℓ₂, mul_one, abs_le] at hinner
    have hgw3 := goemansWilliamsonConstant_mul_le_arccos hinner.1 hinner.2
    simp only [satSdpClause]
    linarith
  · simp at hc

/-- **Goemans–Williamson MAX-2SAT relaxation bound.** For weighted clauses of length at most `2`
and unit vectors `v : Option V → F`, the expected satisfied weight under random-hyperplane rounding
is at least `α * satSdpValue clauses w v` [GoemansWilliamson1995, Section 7.2.1]. -/
theorem goemansWilliamsonConstant_mul_satSdpValue_le_integral (clauses : ι → Clause V)
    (hc : ∀ j, (clauses j).length ≤ 2) {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j)
    {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1) :
    goemansWilliamsonConstant * satSdpValue clauses w v ≤
      ∫ r, satValue clauses w (satHyperplaneAssignment v r) ∂stdGaussian F := by
  unfold satValue satSdpValue
  rw [integral_finsetSum _ fun j _ =>
    integrable_ite_const (stdGaussian F) (measurableSet_clause_eval v (clauses j)) (w j),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hmul : (fun r : F => if (clauses j).eval (satHyperplaneAssignment v r) then w j else 0) =
      fun r : F =>
        w j * (if (clauses j).eval (satHyperplaneAssignment v r) then (1 : ℝ) else 0) := by
    ext r; split_ifs <;> ring
  rw [hmul, integral_const_mul]
  have hcl := mul_le_mul_of_nonneg_left
    (goemansWilliamsonConstant_mul_satSdpClause_le_integral hv (hc j)) (hw j)
  simpa only [mul_left_comm] using hcl

/-- **Goemans–Williamson MAX-2SAT `ε`-optimal guarantee.** If `v` are within `ε` of optimal for
`satSdpValue`, then for every Boolean assignment `σ`, the expected rounded satisfied weight is at
least `α * (satValue clauses w σ - ε)` [GoemansWilliamson1995, Section 7.2.1]. -/
theorem goemansWilliamsonConstant_mul_sub_le_integral (clauses : ι → Clause V)
    (hc : ∀ j, (clauses j).length ≤ 2) {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j)
    {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1) {ε : ℝ}
    (hopt : ∀ v' : Option V → F, (∀ o, ‖v' o‖ = 1) →
      satSdpValue clauses w v' ≤ satSdpValue clauses w v + ε)
    (σ : V → Bool) :
    goemansWilliamsonConstant * (satValue clauses w σ - ε) ≤
      ∫ r, satValue clauses w (satHyperplaneAssignment v r) ∂stdGaussian F :=
  (mul_le_mul_of_nonneg_left (by linarith [satValue_le_satSdpValue_add hc hv hopt σ])
    goemansWilliamsonConstant_nonneg).trans
    (goemansWilliamsonConstant_mul_satSdpValue_le_integral clauses hc hw hv)

/-- **Goemans–Williamson MAX-2SAT exact-optimum guarantee.** -/
theorem goemansWilliamsonConstant_mul_satValue_le_integral (clauses : ι → Clause V)
    (hc : ∀ j, (clauses j).length ≤ 2) {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j)
    {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1)
    (hopt : IsMaxOn (satSdpValue clauses w) {v' | ∀ o, ‖v' o‖ = 1} v) (σ : V → Bool) :
    goemansWilliamsonConstant * satValue clauses w σ ≤
      ∫ r, satValue clauses w (satHyperplaneAssignment v r) ∂stdGaussian F := by
  simpa only [sub_zero] using goemansWilliamsonConstant_mul_sub_le_integral clauses hc hw hv
    (ε := 0) (fun v' hv' => (add_zero (satSdpValue clauses w v)).symm ▸ isMaxOn_iff.1 hopt v' hv') σ

/-- Some hyperplane induces a Boolean assignment achieving the `(α, ε)` MAX-2SAT bound against
every assignment `σ`. -/
theorem exists_forall_goemansWilliamsonConstant_mul_sub_le (clauses : ι → Clause V)
    (hc : ∀ j, (clauses j).length ≤ 2) {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j)
    {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1) {ε : ℝ}
    (hopt : ∀ v' : Option V → F, (∀ o, ‖v' o‖ = 1) →
      satSdpValue clauses w v' ≤ satSdpValue clauses w v + ε) :
    ∃ r : F, ∀ σ : V → Bool,
      goemansWilliamsonConstant * (satValue clauses w σ - ε) ≤
        satValue clauses w (satHyperplaneAssignment v r) := by
  obtain ⟨r, hr⟩ := exists_integral_le
    (integrable_satValue_satHyperplaneAssignment clauses w v (stdGaussian F))
  exact ⟨r, fun σ =>
    (goemansWilliamsonConstant_mul_sub_le_integral clauses hc hw hv hopt σ).trans hr⟩

end SatMeasurable

/-- Optimal unit vectors exist for `satSdpValue` in every nontrivial finite-dimensional `F`. -/
theorem exists_isMaxOn_satSdpValue [FiniteDimensional ℝ F] [Nontrivial F]
    (clauses : ι → Clause V) (w : ι → ℝ) :
    ∃ v : Option V → F, (∀ o, ‖v o‖ = 1) ∧
      IsMaxOn (satSdpValue clauses w) {v' | ∀ o, ‖v' o‖ = 1} v := by
  have hcont : ∀ c : Clause V, Continuous (fun v : Option V → F => satSdpClause v c) := by
    rintro (_ | ⟨ℓ₁, _ | ⟨ℓ₂, _⟩⟩) <;> dsimp only [satSdpClause, litVector]
    · exact continuous_const
    · cases ℓ₁.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
    · cases ℓ₁.2 <;> cases ℓ₂.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  refine NormedSpace.exists_isMaxOn_unitSphereFun ?_
  unfold satSdpValue
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (hcont (clauses j))

end Cslib.Algorithms.Lean.MaxTwoSAT
