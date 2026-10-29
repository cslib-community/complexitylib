/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Polynomial.CoeffNorm1
public import Complexity.Foundations.LinearAlgebra.ExchangeReplacement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Variable copy placement and coefficient norm bounds for polynomial replacement rows

Given the auxiliary exchange matrix `M0`, measurement matrix `measurementMatrix` (`C^B`), and
auxiliary replacement rows `auxReplacementRow` (`P⃗_u(T)`) from
`Complexity.Foundations.LinearAlgebra.ExchangeReplacement`, this module formalizes Section 4.5
(p. 32, equations 4.14–4.16) and the explicit coefficient norm bounds of Lemma 4.6 (p. 33) of the
manuscript *The Exponential Time Hypothesis is False* (`[OpenAI2026ETH]`):

1. **Deterministic copy-index assignment from fiber multiplicity bounds (Section 4.5, p. 32):**
   - For a linearly ordered incidence index type `A` and auxiliary label map `u : A → β`, if every
     fiber `{e : A | u e = y}` has cardinality at most `h`, `fiberRankCopy u h_bound : A → Fin h`
     assigns each incidence `e` its rank `{e' : A | u e' = u e ∧ e' < e}` within its fiber, making
     `fun e => (fiberRankCopy u h_bound e, u e)` injective (`injective_fiberRankCopy_prod`).

2. **Variable copy placement into `Fin h × AuxLabel Q r` (Section 4.5, p. 32, eq. 4.14):**
   - Given a placement `place : A → Fin h × AuxLabel Q r` and variable projection
     `varOf : A → Fin n`, the linear copy/fiber-sum map `copyEmbed place varOf`
     (`ι : (Fin n → K) → (Fin h × AuxLabel Q r → K)`) sums `x (varOf e)` over incidences `e` with
     `place e = p` (placing `x (varOf e)` at `place e` and `0` at unoccupied positions when `place`
     is injective), and `copyProj c` (`π_c`) projects onto copy `c : Fin h`.
   - `varReplacementRow Q r A₀ R place varOf e : Fin n → ℚ[X]`
     (`P⃗_{f,v}(T) = P⃗_{u_{f,v}}(T) π_c ι`) has degree at most `R - 1`
     (`natDegree_varReplacementRow_le`), evaluates at `T = 0` to `δ_{varOf e}` when `place` is
     injective (`eval_varReplacementRow_zero`, `evalVarReplacementRow_zero`), and clears
     denominators to `varReplacementRowScaledInt` upon multiplication by
     `commonDenom Q R = (R - 1)! Q!` (`map_varReplacementRowScaledInt`).

3. **Variable measurement matrices and Definition 3.1 separation (Section 4.5, eqs. 4.15–4.16):**
   - `varGroup a t g = {v : Fin n | a v t = g}` (`S_{t,g}`) partitions `Fin n` into `r` disjoint
     variable groups for each evaluation step `t : Fin Q`.
   - `varMeasurementMatrix Q r A₀ R K place varOf` (`Ĉ = C̃ ι`) and its group restrictions have
     `h * #(measurementIndices Q r A₀ R)` rows per group (`r * h * #(measurementIndices Q r A₀ R)`
     total rows across `g : Fin r`, eq. 4.16).
   - When `place` is injective, every row of `varMeasurementMatrix Q r A₀ R ℤ place varOf` has
     `ℓ₁`-norm at most `r ^ (2 * Q) = D` (`sum_abs_varMeasurementMatrix_le`), so on any
     `{0, 1}`-valued vector its evaluation lies in `[-D, D]`.
   - When `(place e').2.1 = a (varOf e')` for all `e' : A`, Lemma 4.3 transfers directly to
     `Fin n → ℚ`: if `g ≠ (place e).2.2 t` and `ξ` is supported on `varGroup a t g` with
     `(varMeasurementMatrix Q r A₀ R ℚ place varOf).mulVec ξ = 0`, then
     `evalVarReplacementRow Q r A₀ R place varOf e (nodePoint t) ξ = 0`
     (`evalVarReplacementRow_nodePoint_eq_zero_of_kernel`), and `evalVarReplacementRow` at
     `nodePoint t` depends only on `x` restricted to `varGroup a t ((place e).2.2 t)` and
     `(varMeasurementMatrix Q r A₀ R ℚ place varOf).mulVec x`
     (`evalVarReplacementRow_nodePoint_eq_of_eq_on_varGroup`).

4. **Explicit `ℓ₁`-coefficient norm bounds (Lemma 4.6, p. 33):**
   - Reusing the canonical `Polynomial.coeffNorm1` from
     `Complexity.Foundations.Data.Polynomial.CoeffNorm1` and defining `rowNorm1 A u = ∑ y, |A u y|`,
     prove `coeffNorm1_mismatchAnnihilatorScaledInt_le :`
     `(mismatchAnnihilatorScaledInt u y).coeffNorm1 ≤ Q! * 2 ^ Q` and, when `0 < Q` and
     `hI : ∀ a < R - 1, A₀ + a ≤ Q`, prove `rowNorm1_M0ScaledInt_le :`
     `rowNorm1 (M0ScaledInt Q r A₀ R) u ≤ (R - 1)! * R * (4 * Q) ^ (R - 1)` together with the row
     coefficient `ℓ₁`-sum bound
     `≤ commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (4 * Q) ^ (R - 1))` for both
     `auxReplacementRowScaledInt` (`sum_coeffNorm1_auxReplacementRowScaledInt_le`) and, under
     injective `place`, `varReplacementRowScaledInt`
     (`sum_coeffNorm1_varReplacementRowScaledInt_le`).

## Main definitions

* `Cslib.LinearAlgebra.fiberRank`, `Cslib.LinearAlgebra.fiberRankCopy`: deterministic copy index in
  `Fin h` from fiber multiplicity bound `≤ h`.
* `Cslib.LinearAlgebra.copyEmbed`, `Cslib.LinearAlgebra.copyProj`: the linear copy/fiber-sum map
  `ι` into `Fin h × AuxLabel Q r` and copy projection `π_c`.
* `Cslib.LinearAlgebra.varReplacementRow`, `Cslib.LinearAlgebra.evalVarReplacementRow`,
  `Cslib.LinearAlgebra.varReplacementRowScaledInt`: replacement polynomial rows `P⃗_{f,v}(T)` on
  the original `n` variables and their integer-cleared counterparts.
* `Cslib.LinearAlgebra.varGroup`, `Cslib.LinearAlgebra.varGroupRestrict`,
  `Cslib.LinearAlgebra.varMeasurementMatrix`: variable groups `S_{t,g}` and pulled-back measurement
  matrix `Ĉ = C̃ ι`.
* `Cslib.LinearAlgebra.rowNorm1`: matrix row `ℓ₁` norm.

## Main results

* `Cslib.LinearAlgebra.injective_fiberRankCopy_prod`: distinctness of `(c(e), u(e))` when fiber
  multiplicities are at most `h`.
* `Cslib.LinearAlgebra.natDegree_varReplacementRow_le`,
  `Cslib.LinearAlgebra.evalVarReplacementRow_zero`,
  `Cslib.LinearAlgebra.evalVarReplacementRow_nodePoint_eq_zero_of_kernel`,
  `Cslib.LinearAlgebra.evalVarReplacementRow_nodePoint_eq_of_eq_on_varGroup`:
  Definition 3.1 replacement row properties on `Fin n`.
* `Cslib.LinearAlgebra.sum_abs_varMeasurementMatrix_le`,
  `Cslib.LinearAlgebra.abs_varMeasurementMatrix_mulVec_le_of_zero_one`:
  row `ℓ₁`-norm bound `≤ r ^ (2 * Q)` and `[-D, D]` range on `{0, 1}` inputs.
* `Cslib.LinearAlgebra.coeffNorm1_mismatchAnnihilatorScaledInt_le`,
  `Cslib.LinearAlgebra.sum_coeffNorm1_auxReplacementRowScaledInt_le`,
  `Cslib.LinearAlgebra.sum_coeffNorm1_varReplacementRowScaledInt_le`:
  Lemma 4.6 explicit row coefficient `ℓ₁`-sum bounds under `0 < Q` and `∀ a < R - 1, A₀ + a ≤ Q`.

## References

* [OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.LinearAlgebra

open Finset Matrix Polynomial

/-! ### 1. Deterministic copy assignment from fiber multiplicity bounds (Section 4.5, p. 32) -/

/-- Rank of `e : A` within its label fiber `{e' : A | u e' = u e}`, counting strictly smaller
elements `e' < e`. -/
def fiberRank {A β : Type*} [Fintype A] [LinearOrder A] [DecidableEq β]
    (u : A → β) (e : A) : ℕ :=
  #{e' : A | u e' = u e ∧ e' < e}

theorem fiberRank_lt_card_fiber {A β : Type*} [Fintype A] [LinearOrder A] [DecidableEq β]
    (u : A → β) (e : A) :
    fiberRank u e < #{e' : A | u e' = u e} := by
  unfold fiberRank
  refine card_lt_card ⟨fun e' he' => ?_, ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at he' ⊢
    exact he'.1
  · intro hsub
    have he : e ∈ univ.filter (fun e' : A => u e' = u e) := by simp
    have he' := hsub he
    simp at he'

theorem injective_fiberRank_prod {A β : Type*} [Fintype A] [LinearOrder A] [DecidableEq β]
    (u : A → β) :
    Function.Injective (fun e : A => (fiberRank u e, u e)) := by
  intro e₁ e₂ h
  have hu : u e₁ = u e₂ := (Prod.mk.inj h).2
  have hrank : fiberRank u e₁ = fiberRank u e₂ := (Prod.mk.inj h).1
  rcases lt_trichotomy e₁ e₂ with hlt | rfl | hgt
  · exfalso
    have hlt_card : fiberRank u e₁ < fiberRank u e₂ := by
      unfold fiberRank
      refine card_lt_card ⟨fun e' he' => ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and] at he' ⊢
        exact ⟨he'.1.trans hu, he'.2.trans hlt⟩
      · intro hsub
        have he1 : e₁ ∈ univ.filter (fun e' : A => u e' = u e₂ ∧ e' < e₂) := by
          simp [hu, hlt]
        have he1' := hsub he1
        simp at he1'
    exact hlt_card.ne hrank
  · rfl
  · exfalso
    have hlt_card : fiberRank u e₂ < fiberRank u e₁ := by
      unfold fiberRank
      refine card_lt_card ⟨fun e' he' => ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and] at he' ⊢
        exact ⟨he'.1.trans hu.symm, he'.2.trans hgt⟩
      · intro hsub
        have he2 : e₂ ∈ univ.filter (fun e' : A => u e' = u e₁ ∧ e' < e₁) := by
          simp [hu.symm, hgt]
        have he2' := hsub he2
        simp at he2'
    exact hlt_card.ne hrank.symm

/-- Explicit copy index `c(e) ∈ Fin h` assigned to `e : A` when every label fiber of `u : A → β`
has size at most `h` (Section 4.5, p. 32). -/
def fiberRankCopy {A β : Type*} [Fintype A] [LinearOrder A] [DecidableEq β] {h : ℕ}
    (u : A → β) (h_bound : ∀ y : β, #{e : A | u e = y} ≤ h) (e : A) : Fin h :=
  ⟨fiberRank u e, (fiberRank_lt_card_fiber u e).trans_le (h_bound (u e))⟩

/-- All pairs `(fiberRankCopy u h_bound e, u e)` in `Fin h × β` are distinct
(Section 4.5, p. 32). -/
theorem injective_fiberRankCopy_prod {A β : Type*} [Fintype A] [LinearOrder A] [DecidableEq β]
    {h : ℕ} (u : A → β) (h_bound : ∀ y : β, #{e : A | u e = y} ≤ h) :
    Function.Injective (fun e : A => (fiberRankCopy u h_bound e, u e)) := by
  intro e₁ e₂ hEq
  refine injective_fiberRank_prod u (Prod.ext ?_ (Prod.mk.inj hEq).2)
  exact congrArg Fin.val (Prod.mk.inj hEq).1

/-! ### 2. Variable copy placement into `Fin h × AuxLabel Q r` (Section 4.5, p. 32, eq. 4.14) -/

/-- The linear copy/fiber-sum map `ι : (Fin n → K) → (Fin h × AuxLabel Q r → K)` summing
`x (varOf e)` over incidences `e : A` with `place e = p` (which places `x (varOf e)` at position
`place e` and `0` at unoccupied positions when `place` is injective; Section 4.5, p. 32). -/
def copyEmbed {A : Type*} [Fintype A] {n h Q r : ℕ} {K : Type*} [AddCommMonoid K]
    (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (x : Fin n → K) (p : Fin h × AuxLabel Q r) : K :=
  ∑ e ∈ univ.filter (fun e : A => place e = p), x (varOf e)

/-- The projection `π_c : (Fin h × AuxLabel Q r → K) → (AuxLabel Q r → K)` onto copy `c : Fin h`
(Section 4.5, p. 32). -/
def copyProj {h Q r : ℕ} {K : Type*} (c : Fin h)
    (η : Fin h × AuxLabel Q r → K) (u : AuxLabel Q r) : K :=
  η (c, u)

@[simp]
theorem copyEmbed_zero {A : Type*} [Fintype A] {n h Q r : ℕ} {K : Type*} [AddCommMonoid K]
    (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n) :
    copyEmbed place varOf (0 : Fin n → K) = 0 := by
  ext p
  simp [copyEmbed]

theorem copyEmbed_add {A : Type*} [Fintype A] {n h Q r : ℕ} {K : Type*} [AddCommMonoid K]
    (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n) (x₁ x₂ : Fin n → K) :
    copyEmbed place varOf (x₁ + x₂) = copyEmbed place varOf x₁ + copyEmbed place varOf x₂ := by
  ext p
  simp [copyEmbed, sum_add_distrib]

theorem copyEmbed_sub {A : Type*} [Fintype A] {n h Q r : ℕ} {K : Type*} [AddCommGroup K]
    (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n) (x₁ x₂ : Fin n → K) :
    copyEmbed place varOf (x₁ - x₂) = copyEmbed place varOf x₁ - copyEmbed place varOf x₂ := by
  ext p
  simp [copyEmbed, sum_sub_distrib]

@[simp]
theorem copyProj_zero {h Q r : ℕ} {K : Type*} [Zero K] (c : Fin h) :
    copyProj c (0 : Fin h × AuxLabel Q r → K) = 0 :=
  rfl

theorem copyProj_add {h Q r : ℕ} {K : Type*} [Add K] (c : Fin h)
    (η₁ η₂ : Fin h × AuxLabel Q r → K) :
    copyProj c (η₁ + η₂) = copyProj c η₁ + copyProj c η₂ :=
  rfl

theorem copyProj_sub {h Q r : ℕ} {K : Type*} [Sub K] (c : Fin h)
    (η₁ η₂ : Fin h × AuxLabel Q r → K) :
    copyProj c (η₁ - η₂) = copyProj c η₁ - copyProj c η₂ :=
  rfl

/-- When `place` is injective, `copyEmbed place varOf x (place e)` extracts `x (varOf e)`. -/
theorem copyEmbed_apply_place {A : Type*} [Fintype A] {n h Q r : ℕ}
    {K : Type*} [AddCommMonoid K] {place : A → Fin h × AuxLabel Q r}
    (hinj : Function.Injective place) (varOf : A → Fin n) (x : Fin n → K) (e : A) :
    copyEmbed place varOf x (place e) = x (varOf e) := by
  classical
  unfold copyEmbed
  have hfilter : univ.filter (fun e' : A => place e' = place e) = {e} := by
    ext e'
    simp [hinj.eq_iff]
  rw [hfilter, sum_singleton]

/-- Double-sum interchange for `copyProj c (copyEmbed place varOf x)`: summing `f y * (π_c (ι x)) y`
over `y : AuxLabel Q r` equals summing over `v : Fin n` the accumulated coefficients at copy `c`. -/
private theorem sum_mul_copyProj_copyEmbed {A : Type*} [Fintype A] {n h Q r : ℕ}
    {K : Type*} [CommRing K] (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (c : Fin h) (f : AuxLabel Q r → K) (x : Fin n → K) :
    (∑ y : AuxLabel Q r, f y * copyProj c (copyEmbed place varOf x) y) =
      ∑ v : Fin n,
        (∑ e' ∈ univ.filter (fun e' : A => (place e').1 = c ∧ varOf e' = v),
          f (place e').2) * x v := by
  classical
  simp only [copyProj, copyEmbed, mul_sum, sum_mul]
  have hL :
      (∑ y : AuxLabel Q r,
          ∑ e' ∈ univ.filter (fun e' : A => place e' = (c, y)), f y * x (varOf e')) =
        ∑ y : AuxLabel Q r,
          ∑ e' ∈ univ.filter (fun e' : A => (place e').1 = c ∧ (place e').2 = y),
            f (place e').2 * x (varOf e') := by
    refine sum_congr rfl fun y _ => sum_congr ?_ fun e' he' => ?_
    · ext e'
      simp [Prod.ext_iff]
    · simp only [mem_filter, mem_univ, true_and] at he'
      rw [he'.2]
  rw [hL, ← sum_biUnion]
  · have hU₁ :
        (univ.biUnion fun y : AuxLabel Q r =>
            univ.filter (fun e' : A => (place e').1 = c ∧ (place e').2 = y)) =
          univ.filter (fun e' : A => (place e').1 = c) := by
      ext e'
      simp
    have hU₂ :
        (univ.biUnion fun v : Fin n =>
            univ.filter (fun e' : A => (place e').1 = c ∧ varOf e' = v)) =
          univ.filter (fun e' : A => (place e').1 = c) := by
      ext e'
      simp
    rw [hU₁, ← hU₂, sum_biUnion]
    · refine sum_congr rfl fun v _ => sum_congr rfl fun e' he' => ?_
      simp only [mem_filter, mem_univ, true_and] at he'
      rw [he'.2]
    · intro v₁ _ v₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro e' h1 h2
      simp only [mem_filter, mem_univ, true_and] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  · intro y₁ _ y₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro e' h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    exact hne (h1.2.symm.trans h2.2)

/-- The replacement polynomial row `P⃗_e(T) = P⃗_{u_e}(T) π_{c(e)} ι ∈ (Fin n → ℚ[X])` on the
original variables `Fin n` (eq. 4.14, p. 32). -/
noncomputable def varReplacementRow {A : Type*} [Fintype A] (Q r A₀ R : ℕ) {n h : ℕ}
    (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (e : A) (v : Fin n) : ℚ[X] :=
  ∑ e' ∈ univ.filter (fun e' : A => (place e').1 = (place e).1 ∧ varOf e' = v),
    auxReplacementRow Q r A₀ R (place e).2 (place e').2

/-- Pairing `⟨P⃗_e(t), x⟩` of `varReplacementRow Q r A₀ R place varOf e` with `x : Fin n → ℚ`
at `T = t` (Section 4.5, p. 32). -/
noncomputable def evalVarReplacementRow {A : Type*} [Fintype A] (Q r A₀ R : ℕ) {n h : ℕ}
    (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (e : A) (t : ℚ) (x : Fin n → ℚ) : ℚ :=
  ∑ v : Fin n, (varReplacementRow Q r A₀ R place varOf e v).eval t * x v

/-- The scaled integer replacement row `d_den P⃗_e(T) ∈ (Fin n → ℤ[X])` on the original variables
(Lemma 4.6, p. 33). -/
noncomputable def varReplacementRowScaledInt {A : Type*} [Fintype A] (Q r A₀ R : ℕ) {n h : ℕ}
    (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (e : A) (v : Fin n) : ℤ[X] :=
  ∑ e' ∈ univ.filter (fun e' : A => (place e').1 = (place e).1 ∧ varOf e' = v),
    auxReplacementRowScaledInt Q r A₀ R (place e).2 (place e').2

/-- **Equation (4.14) identity (p. 32)**: evaluating `varReplacementRow` on `x : Fin n → ℚ`
equals evaluating `auxReplacementRow` at `(place e).2` on `π_{(place e).1} (ι x)`. -/
theorem evalVarReplacementRow_eq_evalAuxReplacementRow {A : Type*} [Fintype A]
    (Q r A₀ R : ℕ) {n h : ℕ} (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (e : A) (t : ℚ) (x : Fin n → ℚ) :
    evalVarReplacementRow Q r A₀ R place varOf e t x =
      evalAuxReplacementRow Q r A₀ R (place e).2 t
        (copyProj (place e).1 (copyEmbed place varOf x)) := by
  unfold evalVarReplacementRow evalAuxReplacementRow varReplacementRow
  rw [sum_mul_copyProj_copyEmbed]
  refine sum_congr rfl fun v _ => ?_
  rw [Polynomial.eval_finsetSum]

/-- Every entry of `varReplacementRow Q r A₀ R place varOf e` has degree at most `R - 1`
(Section 4.5, p. 32). -/
theorem natDegree_varReplacementRow_le {A : Type*} [Fintype A] (Q r A₀ R : ℕ) {n h : ℕ}
    (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n) (e : A) (v : Fin n) :
    (varReplacementRow Q r A₀ R place varOf e v).natDegree ≤ R - 1 := by
  unfold varReplacementRow
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  exact ⟨Nat.zero_le _,
    fun e' _ => natDegree_auxReplacementRow_le Q r A₀ R (place e).2 (place e').2⟩

/-- When `place` is injective, `varReplacementRow` evaluates at `T = 0` to `δ_{varOf e}`
(Section 4.5, p. 32). -/
theorem eval_varReplacementRow_zero {A : Type*} [Fintype A]
    (Q r A₀ R : ℕ) {n h : ℕ} {place : A → Fin h × AuxLabel Q r}
    (hinj : Function.Injective place) (varOf : A → Fin n) (e : A) (v : Fin n) :
    (varReplacementRow Q r A₀ R place varOf e v).eval 0 = if varOf e = v then 1 else 0 := by
  classical
  unfold varReplacementRow
  rw [Polynomial.eval_finsetSum]
  simp only [eval_auxReplacementRow_zero]
  have h1 :
      ∀ e' ∈ univ.filter (fun e' : A => (place e').1 = (place e).1 ∧ varOf e' = v),
        ((place e).2 = (place e').2 ↔ e' = e) := by
    intro e' he'
    simp only [mem_filter, mem_univ, true_and] at he'
    constructor
    · intro h2
      exact hinj (Prod.ext he'.1 h2.symm)
    · rintro rfl
      rfl
  have hsum :
      (∑ e' ∈ univ.filter (fun e' : A => (place e').1 = (place e).1 ∧ varOf e' = v),
          if (place e).2 = (place e').2 then (1 : ℚ) else 0) =
        ∑ e' ∈ univ.filter (fun e' : A => (place e').1 = (place e).1 ∧ varOf e' = v),
          if e' = e then (1 : ℚ) else 0 :=
    sum_congr rfl fun e' he' => if_congr (h1 e' he') rfl rfl
  rw [hsum, sum_ite_eq']
  simp

/-- When `place` is injective, `⟨P⃗_e(0), x⟩ = x (varOf e)` (Section 4.5, p. 32). -/
theorem evalVarReplacementRow_zero {A : Type*} [Fintype A]
    (Q r A₀ R : ℕ) {n h : ℕ} {place : A → Fin h × AuxLabel Q r}
    (hinj : Function.Injective place) (varOf : A → Fin n) (e : A) (x : Fin n → ℚ) :
    evalVarReplacementRow Q r A₀ R place varOf e 0 x = x (varOf e) := by
  rw [evalVarReplacementRow_eq_evalAuxReplacementRow, evalAuxReplacementRow_zero, copyProj,
    Prod.mk.eta, copyEmbed_apply_place hinj]

/-- **Lemma 4.6 for `varReplacementRow` (p. 33)**: multiplying `varReplacementRow` by
`commonDenom Q R = (R - 1)! Q!` gives the integer polynomial `varReplacementRowScaledInt`. -/
theorem map_varReplacementRowScaledInt {A : Type*} [Fintype A] (Q r A₀ R : ℕ) {n h : ℕ}
    (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n) (e : A) (v : Fin n) :
    (varReplacementRowScaledInt Q r A₀ R place varOf e v).map (Int.castRingHom ℚ) =
      (commonDenom Q R : ℚ) • varReplacementRow Q r A₀ R place varOf e v := by
  unfold varReplacementRowScaledInt varReplacementRow
  rw [Polynomial.map_sum, smul_sum]
  exact sum_congr rfl fun e' _ => map_auxReplacementRowScaledInt Q r A₀ R (place e).2 (place e').2

/-! ### 3. Variable measurement matrices and Definition 3.1 separation (Section 4.5, p. 32) -/

/-- The actual-variable group `S_{t, g} = {v : Fin n | a v t = g}` (eq. 4.14, p. 32). -/
def varGroup {n Q r : ℕ} (a : Fin n → Fin Q → Fin r) (t : Fin Q) (g : Fin r) : Finset (Fin n) :=
  univ.filter (fun v => a v t = g)

@[simp]
theorem mem_varGroup {n Q r : ℕ} {a : Fin n → Fin Q → Fin r} {t : Fin Q} {g : Fin r}
    {v : Fin n} :
    v ∈ varGroup a t g ↔ a v t = g := by
  simp [varGroup]

theorem disjoint_varGroup {n Q r : ℕ} (a : Fin n → Fin Q → Fin r) (t : Fin Q) {g₁ g₂ : Fin r}
    (hne : g₁ ≠ g₂) :
    Disjoint (varGroup a t g₁) (varGroup a t g₂) := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  rw [mem_varGroup] at hv1 hv2
  exact hne (hv1.symm.trans hv2)

theorem biUnion_varGroup {n Q r : ℕ} (a : Fin n → Fin Q → Fin r) (t : Fin Q) :
    univ.biUnion (varGroup a t) = univ := by
  ext v
  simp [mem_biUnion]

/-- Restriction of `x : Fin n → K` to `varGroup a t g`, extended by zero outside
`varGroup a t g`. -/
def varGroupRestrict {n Q r : ℕ} {K : Type*} [Zero K] (a : Fin n → Fin Q → Fin r)
    (t : Fin Q) (g : Fin r) (x : Fin n → K) : Fin n → K :=
  fun v => if v ∈ varGroup a t g then x v else 0

theorem sum_varGroupRestrict {n Q r : ℕ} {K : Type*} [AddCommMonoid K]
    (a : Fin n → Fin Q → Fin r) (t : Fin Q) (x : Fin n → K) :
    (∑ g : Fin r, varGroupRestrict a t g x) = x := by
  ext v
  simp [varGroupRestrict]

/-- The pulled-back measurement matrix `Ĉ = C̃ ι` on `Fin n` with rows indexed by
`Fin h × measurementIndices Q r A₀ R` (eq. 4.15, p. 32). -/
def varMeasurementMatrix {A : Type*} [Fintype A] (Q r A₀ R : ℕ) {n h : ℕ}
    (K : Type*) [CommRing K] (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n) :
    Matrix (Fin h × measurementIndices Q r A₀ R) (Fin n) K :=
  fun p v =>
    ∑ e' ∈ univ.filter (fun e' : A => (place e').1 = p.1 ∧ varOf e' = v),
      measurementMatrix Q r A₀ R K p.2 (place e').2

/-- The group-restricted measurement matrix `C_{t,g} = Ĉ|_{S_{t,g}}` keeping columns in
`varGroup a t g` (eq. 4.15, p. 32). -/
def groupMeasurementMatrix {A : Type*} [Fintype A] (Q r A₀ R : ℕ) {n h : ℕ}
    (K : Type*) [CommRing K] (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (a : Fin n → Fin Q → Fin r) (t : Fin Q) (g : Fin r) :
    Matrix (Fin h × measurementIndices Q r A₀ R) (varGroup a t g) K :=
  fun p v => varMeasurementMatrix Q r A₀ R K place varOf p v.1

/-- **Equation (4.16) row count identity (p. 32)**: each of the `r` matrices `C_{t,g}` has
`h * #(measurementIndices Q r A₀ R)` rows, so their total row count across `g : Fin r` is
`r * h * #(measurementIndices Q r A₀ R)`. -/
theorem sum_card_rows_groupMeasurementMatrix (Q r A₀ R h : ℕ) :
    (∑ _g : Fin r, Fintype.card (Fin h × measurementIndices Q r A₀ R)) =
      r * h * #(measurementIndices Q r A₀ R) := by
  simp [Fintype.card_prod, Fintype.card_coe, mul_assoc]

/-- **Equation (4.16) row count bound (p. 32)**: if `h ≤ h_bound` and
`#(measurementIndices Q r A₀ R) ≤ c_bound`, then the total number of measurement rows across all
`r` variable groups is at most `r * h_bound * c_bound`. -/
theorem sum_card_rows_groupMeasurementMatrix_le (Q r A₀ R h h_bound c_bound : ℕ)
    (hh : h ≤ h_bound) (hc : #(measurementIndices Q r A₀ R) ≤ c_bound) :
    (∑ _g : Fin r, Fintype.card (Fin h × measurementIndices Q r A₀ R)) ≤
      r * h_bound * c_bound := by
  rw [sum_card_rows_groupMeasurementMatrix]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left r hh) hc

/-- **Equation (4.15) action identity (p. 32)**: the `(c, β)`-entry of `(Ĉ x)` equals the
`β`-entry of `C^B (π_c (ι x))`. -/
theorem varMeasurementMatrix_mulVec {A : Type*} [Fintype A] (Q r A₀ R : ℕ) {n h : ℕ}
    (K : Type*) [CommRing K] (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (x : Fin n → K) (c : Fin h) (β : measurementIndices Q r A₀ R) :
    (varMeasurementMatrix Q r A₀ R K place varOf).mulVec x (c, β) =
      (measurementMatrix Q r A₀ R K).mulVec
        (copyProj c (copyEmbed place varOf x)) β := by
  simp only [Matrix.mulVec, dotProduct, varMeasurementMatrix]
  exact (sum_mul_copyProj_copyEmbed place varOf c (measurementMatrix Q r A₀ R K β) x).symm

/-- `Ĉ x = 0` iff `C^B (π_c (ι x)) = 0` for every copy `c : Fin h` (p. 32). -/
theorem varMeasurementMatrix_mulVec_eq_zero_iff {A : Type*} [Fintype A] (Q r A₀ R : ℕ) {n h : ℕ}
    (K : Type*) [CommRing K] (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (x : Fin n → K) :
    (varMeasurementMatrix Q r A₀ R K place varOf).mulVec x = 0 ↔
      ∀ c : Fin h,
        (measurementMatrix Q r A₀ R K).mulVec (copyProj c (copyEmbed place varOf x)) = 0 := by
  constructor
  · intro h0 c
    ext β
    rw [← varMeasurementMatrix_mulVec]
    exact congrFun h0 (c, β)
  · intro h0
    ext ⟨c, β⟩
    rw [varMeasurementMatrix_mulVec]
    exact congrFun (h0 c) β

/-- The full measurement vector `Ĉ x` is the sum over `g : Fin r` of the group measurements
`Ĉ (x|_{S_{t,g}})`. -/
theorem sum_varMeasurementMatrix_mulVec_varGroupRestrict {A : Type*} [Fintype A]
    (Q r A₀ R : ℕ) {n h : ℕ} (K : Type*) [CommRing K]
    (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (a : Fin n → Fin Q → Fin r) (t : Fin Q) (x : Fin n → K) :
    (∑ g : Fin r,
        (varMeasurementMatrix Q r A₀ R K place varOf).mulVec (varGroupRestrict a t g x)) =
      (varMeasurementMatrix Q r A₀ R K place varOf).mulVec x := by
  ext p
  have hsum := congrFun (sum_varGroupRestrict a t x)
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct] at hsum ⊢
  rw [Finset.sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [← mul_sum, hsum v]

/-- If `(place e').2.1 = a (varOf e')` for all `e' : A` and `ξ : Fin n → K` vanishes outside
`varGroup a t g`, then for every copy `c : Fin h`, `copyProj c (copyEmbed place varOf ξ)` vanishes
outside `auxGroup t g` (Section 4.5, p. 32). -/
theorem copyProj_copyEmbed_eq_zero_of_not_mem_auxGroup {A : Type*} [Fintype A]
    {n h Q r : ℕ} {K : Type*} [AddCommMonoid K]
    (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n) (a : Fin n → Fin Q → Fin r)
    (hcompat : ∀ e' : A, (place e').2.1 = a (varOf e'))
    (t : Fin Q) (g : Fin r) (ξ : Fin n → K)
    (hsupp : ∀ v, v ∉ varGroup a t g → ξ v = 0)
    (c : Fin h) {y : AuxLabel Q r} (hy : y ∉ auxGroup t g) :
    copyProj c (copyEmbed place varOf ξ) y = 0 := by
  unfold copyProj copyEmbed
  refine sum_eq_zero fun e' he' => ?_
  simp only [mem_filter, mem_univ, true_and] at he'
  refine hsupp (varOf e') ?_
  rw [mem_varGroup]
  intro hvg
  apply hy
  rw [mem_auxGroup]
  have hy_eq : (place e').2 = y := (Prod.mk.inj he').2
  rw [← hy_eq, hcompat e', hvg]

/-- **Definition 3.1 kernel separation on `Fin n` (Section 4.5, p. 32)**: when
`(place e').2.1 = a (varOf e')` for all `e' : A`, if `g ≠ (place e).2.2 t`, `ξ : Fin n → ℚ` is
supported on `varGroup a t g`, and `(varMeasurementMatrix Q r A₀ R ℚ place varOf).mulVec ξ = 0`,
then `evalVarReplacementRow Q r A₀ R place varOf e (nodePoint t) ξ = 0`. -/
theorem evalVarReplacementRow_nodePoint_eq_zero_of_kernel {A : Type*} [Fintype A]
    (Q r A₀ R : ℕ) {n h : ℕ} (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (a : Fin n → Fin Q → Fin r) (hcompat : ∀ e' : A, (place e').2.1 = a (varOf e'))
    (e : A) (t : Fin Q) (g : Fin r) (hg : g ≠ (place e).2.2 t)
    (ξ : Fin n → ℚ) (hsupp : ∀ v, v ∉ varGroup a t g → ξ v = 0)
    (hker : (varMeasurementMatrix Q r A₀ R ℚ place varOf).mulVec ξ = 0) :
    evalVarReplacementRow Q r A₀ R place varOf e (nodePoint t) ξ = 0 := by
  rw [evalVarReplacementRow_eq_evalAuxReplacementRow]
  have hker_c := (varMeasurementMatrix_mulVec_eq_zero_iff Q r A₀ R ℚ place varOf ξ).1 hker
    (place e).1
  exact evalAuxReplacementRow_nodePoint_eq_zero_of_kernel Q r A₀ R (place e).2 t g hg
    (copyProj (place e).1 (copyEmbed place varOf ξ))
    (fun y hy =>
      copyProj_copyEmbed_eq_zero_of_not_mem_auxGroup place varOf a hcompat t g ξ hsupp
        (place e).1 hy)
    hker_c

/-- **Determination by assigned variable group and measurements (Section 4.5, p. 32)**: at
`T = nodePoint t`, `⟨P⃗_e(nodePoint t), x⟩` depends only on `x` restricted to
`varGroup a t ((place e).2.2 t)` and `(varMeasurementMatrix Q r A₀ R ℚ place varOf).mulVec x`. -/
theorem evalVarReplacementRow_nodePoint_eq_of_eq_on_varGroup {A : Type*} [Fintype A]
    (Q r A₀ R : ℕ) {n h : ℕ} (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (a : Fin n → Fin Q → Fin r) (hcompat : ∀ e' : A, (place e').2.1 = a (varOf e'))
    (e : A) (t : Fin Q) (x₁ x₂ : Fin n → ℚ)
    (hgroup : ∀ v ∈ varGroup a t ((place e).2.2 t), x₁ v = x₂ v)
    (hmeas : (varMeasurementMatrix Q r A₀ R ℚ place varOf).mulVec x₁ =
      (varMeasurementMatrix Q r A₀ R ℚ place varOf).mulVec x₂) :
    evalVarReplacementRow Q r A₀ R place varOf e (nodePoint t) x₁ =
      evalVarReplacementRow Q r A₀ R place varOf e (nodePoint t) x₂ := by
  rw [evalVarReplacementRow_eq_evalAuxReplacementRow,
    evalVarReplacementRow_eq_evalAuxReplacementRow]
  refine evalAuxReplacementRow_nodePoint_eq_of_eq_on_auxGroup Q r A₀ R (place e).2 t _ _ ?_ ?_
  · intro y hy
    rw [mem_auxGroup] at hy
    unfold copyProj copyEmbed
    refine sum_congr rfl fun e' he' => ?_
    simp only [mem_filter, mem_univ, true_and] at he'
    refine hgroup (varOf e') ?_
    rw [mem_varGroup]
    have hy_eq : (place e').2 = y := (Prod.mk.inj he').2
    rw [← hcompat e', hy_eq, hy]
  · ext β
    rw [← varMeasurementMatrix_mulVec, ← varMeasurementMatrix_mulVec, hmeas]

/-- When `place` is injective, every row of `varMeasurementMatrix Q r A₀ R ℤ place varOf` has
absolute row sum at most `r ^ (2 * Q) = D` (Section 4.5, p. 32). -/
theorem sum_abs_varMeasurementMatrix_le {A : Type*} [Fintype A] (Q r A₀ R : ℕ) {n h : ℕ}
    {place : A → Fin h × AuxLabel Q r} (hinj : Function.Injective place) (varOf : A → Fin n)
    (p : Fin h × measurementIndices Q r A₀ R) :
    (∑ v : Fin n, |varMeasurementMatrix Q r A₀ R ℤ place varOf p v|) ≤ (r ^ (2 * Q) : ℤ) := by
  classical
  have htri :
      (∑ v : Fin n, |varMeasurementMatrix Q r A₀ R ℤ place varOf p v|) ≤
        ∑ v : Fin n,
          ∑ e' ∈ univ.filter (fun e' : A => (place e').1 = p.1 ∧ varOf e' = v),
            |measurementMatrix Q r A₀ R ℤ p.2 (place e').2| :=
    sum_le_sum fun v _ => abs_sum_le_sum_abs _ _
  have hU :
      (∑ v : Fin n,
          ∑ e' ∈ univ.filter (fun e' : A => (place e').1 = p.1 ∧ varOf e' = v),
            |measurementMatrix Q r A₀ R ℤ p.2 (place e').2|) =
        ∑ e' ∈ univ.filter (fun e' : A => (place e').1 = p.1),
          |measurementMatrix Q r A₀ R ℤ p.2 (place e').2| := by
    rw [← sum_biUnion]
    · congr 1
      ext e'
      simp
    · intro v₁ _ v₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro e' h1 h2
      simp only [mem_filter, mem_univ, true_and] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  have h1 :
      (∑ e' ∈ univ.filter (fun e' : A => (place e').1 = p.1),
          |measurementMatrix Q r A₀ R ℤ p.2 (place e').2|) ≤
        #(univ.filter (fun e' : A => (place e').1 = p.1)) := by
    calc
      (∑ e' ∈ univ.filter (fun e' : A => (place e').1 = p.1),
          |measurementMatrix Q r A₀ R ℤ p.2 (place e').2|) ≤
        ∑ _e' ∈ univ.filter (fun e' : A => (place e').1 = p.1), (1 : ℤ) :=
          sum_le_sum fun e' _ => abs_eigenvecInt_le_one p.2.1 (place e').2
      _ = #(univ.filter (fun e' : A => (place e').1 = p.1)) := by simp
  have hcard :
      #(univ.filter (fun e' : A => (place e').1 = p.1)) ≤ r ^ (2 * Q) := by
    have hinj_on :
        Set.InjOn (fun e' : A => (place e').2)
          (univ.filter (fun e' : A => (place e').1 = p.1)) := by
      intro e₁ he₁ e₂ he₂ h2
      simp only [mem_coe, mem_filter, mem_univ, true_and] at he₁ he₂
      exact hinj (Prod.ext (he₁.trans he₂.symm) h2)
    calc
      #(univ.filter (fun e' : A => (place e').1 = p.1)) =
          #((univ.filter (fun e' : A => (place e').1 = p.1)).image (fun e' : A => (place e').2)) :=
        (card_image_of_injOn hinj_on).symm
      _ ≤ #(univ : Finset (AuxLabel Q r)) := card_le_univ _
      _ = r ^ (2 * Q) := by rw [card_univ, card_auxLabel]
  exact htri.trans (by rw [hU]; exact h1.trans (by exact_mod_cast hcard))

/-- On any `{0, 1}`-valued vector `x : Fin n → ℤ`, every coordinate of
`(varMeasurementMatrix Q r A₀ R ℤ place varOf).mulVec x` has absolute value at most
`r ^ (2 * Q) = D` (and thus lies in `[-D, D] ∩ ℤ`, Section 4.5, p. 32). -/
theorem abs_varMeasurementMatrix_mulVec_le_of_zero_one {A : Type*} [Fintype A]
    (Q r A₀ R : ℕ) {n h : ℕ} {place : A → Fin h × AuxLabel Q r}
    (hinj : Function.Injective place) (varOf : A → Fin n)
    (x : Fin n → ℤ) (hx : ∀ v : Fin n, x v = 0 ∨ x v = 1)
    (p : Fin h × measurementIndices Q r A₀ R) :
    |(varMeasurementMatrix Q r A₀ R ℤ place varOf).mulVec x p| ≤ (r ^ (2 * Q) : ℤ) := by
  simp only [Matrix.mulVec, dotProduct]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun v _ => ?_).trans (sum_abs_varMeasurementMatrix_le Q r A₀ R hinj varOf p)
  rw [abs_mul]
  rcases hx v with h0 | h1
  · simp [h0]
  · simp [h1]

/-! ### 4. Explicit `ℓ₁`-coefficient norm bounds (Lemma 4.6, p. 33) -/

private theorem coeffNorm1_prod_C_sub_X_le {Q : ℕ} (E : Finset (Fin Q)) :
    (∏ s ∈ E, (C ((s.1 : ℤ) + 1) - X)).coeffNorm1 ≤ ∏ s ∈ E, ((s.1 + 1) + 1) := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | insert s E hs ih =>
    rw [prod_insert hs, prod_insert hs]
    have hnat : ((s.1 : ℤ) + 1).natAbs = s.1 + 1 := by omega
    calc
      ((C ((s.1 : ℤ) + 1) - X) * ∏ t ∈ E, (C ((t.1 : ℤ) + 1) - X)).coeffNorm1 ≤
          (((s.1 : ℤ) + 1).natAbs + 1) *
            (∏ t ∈ E, (C ((t.1 : ℤ) + 1) - X)).coeffNorm1 :=
        coeffNorm1_C_sub_X_mul_le _ _
      _ = ((s.1 + 1) + 1) * (∏ t ∈ E, (C ((t.1 : ℤ) + 1) - X)).coeffNorm1 := by
        rw [hnat]
      _ ≤ ((s.1 + 1) + 1) * ∏ t ∈ E, ((t.1 + 1) + 1) :=
        Nat.mul_le_mul_left _ ih

private theorem prod_add_one_add_one_le {Q : ℕ} (E : Finset (Fin Q)) :
    (∏ s ∈ E, ((s.1 + 1) + 1)) ≤ ∏ s ∈ E, (2 * (s.1 + 1)) := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | insert s E hs ih =>
    rw [prod_insert hs, prod_insert hs]
    exact Nat.mul_le_mul (by omega) ih

/-- **Lemma 4.6 annihilator norm bound (p. 33)**:
`‖Q! φ_{u,y}‖₁ ≤ Q! * 2 ^ Q` (i.e. `‖φ_{u,y}‖₁ ≤ 2 ^ Q`). -/
theorem coeffNorm1_mismatchAnnihilatorScaledInt_le {Q r : ℕ} (u y : AuxLabel Q r) :
    (mismatchAnnihilatorScaledInt u y).coeffNorm1 ≤ Q.factorial * 2 ^ Q := by
  unfold mismatchAnnihilatorScaledInt
  have hcast :
      (∏ s ∈ (mismatchSet u y)ᶜ, ((s.1 : ℤ) + 1)) =
        ((∏ s ∈ (mismatchSet u y)ᶜ, (s.1 + 1) : ℕ) : ℤ) := by
    push_cast
    rfl
  have hnat :
      (∏ s ∈ (mismatchSet u y)ᶜ, ((s.1 : ℤ) + 1)).natAbs =
        ∏ s ∈ (mismatchSet u y)ᶜ, (s.1 + 1) := by
    rw [hcast, Int.natAbs_natCast]
  calc
    (C (∏ s ∈ (mismatchSet u y)ᶜ, ((s.1 : ℤ) + 1)) *
        ∏ s ∈ mismatchSet u y, (C ((s.1 : ℤ) + 1) - X)).coeffNorm1 ≤
      (∏ s ∈ (mismatchSet u y)ᶜ, ((s.1 : ℤ) + 1)).natAbs *
        (∏ s ∈ mismatchSet u y, (C ((s.1 : ℤ) + 1) - X)).coeffNorm1 :=
      coeffNorm1_C_mul_le _ _
    _ = (∏ s ∈ (mismatchSet u y)ᶜ, (s.1 + 1)) *
        (∏ s ∈ mismatchSet u y, (C ((s.1 : ℤ) + 1) - X)).coeffNorm1 := by
      rw [hnat]
    _ ≤ (∏ s ∈ (mismatchSet u y)ᶜ, (s.1 + 1)) *
        ∏ s ∈ mismatchSet u y, ((s.1 + 1) + 1) :=
      Nat.mul_le_mul_left _ (coeffNorm1_prod_C_sub_X_le _)
    _ ≤ (∏ s ∈ (mismatchSet u y)ᶜ, (s.1 + 1)) *
        ∏ s ∈ mismatchSet u y, (2 * (s.1 + 1)) :=
      Nat.mul_le_mul_left _ (prod_add_one_add_one_le _)
    _ = 2 ^ #(mismatchSet u y) * Q.factorial := by
      rw [prod_mul_distrib, prod_const, ← mul_assoc,
        mul_comm (∏ s ∈ (mismatchSet u y)ᶜ, (s.1 + 1)) (2 ^ #(mismatchSet u y)),
        mul_assoc, prod_compl_mul_prod,
        Fin.prod_univ_eq_prod_range (fun i => i + 1) Q,
        Finset.prod_range_add_one_eq_factorial]
    _ ≤ Q.factorial * 2 ^ Q := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega) ((card_le_univ _).trans (by simp)))

/-- Integer-cast form of `coeffNorm1_mismatchAnnihilatorScaledInt_le`. -/
theorem natCast_coeffNorm1_mismatchAnnihilatorScaledInt_le {Q r : ℕ} (u y : AuxLabel Q r) :
    ((mismatchAnnihilatorScaledInt u y).coeffNorm1 : ℤ) ≤ (Q.factorial : ℤ) * 2 ^ Q := by
  exact_mod_cast coeffNorm1_mismatchAnnihilatorScaledInt_le u y

/-- The row `ℓ₁`-norm `∑ y, |A u y|` of a matrix `A` at row `u` (Lemma 4.6, p. 33). -/
def rowNorm1 {Q r : ℕ} (A : Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ) (u : AuxLabel Q r) : ℤ :=
  ∑ y : AuxLabel Q r, |A u y|

theorem rowNorm1_nonneg {Q r : ℕ} (A : Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ)
    (u : AuxLabel Q r) :
    0 ≤ rowNorm1 A u :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem rowNorm1_add_le {Q r : ℕ} (A B : Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ)
    (u : AuxLabel Q r) :
    rowNorm1 (A + B) u ≤ rowNorm1 A u + rowNorm1 B u := by
  unfold rowNorm1
  rw [← sum_add_distrib]
  exact sum_le_sum fun y _ => abs_add_le (A u y) (B u y)

theorem rowNorm1_sub_le {Q r : ℕ} (A B : Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ)
    (u : AuxLabel Q r) :
    rowNorm1 (A - B) u ≤ rowNorm1 A u + rowNorm1 B u := by
  unfold rowNorm1
  rw [← sum_add_distrib]
  exact sum_le_sum fun y _ => abs_sub (A u y) (B u y)

theorem rowNorm1_sum_le {Q r : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ) (u : AuxLabel Q r) :
    rowNorm1 (∑ i ∈ s, f i) u ≤ ∑ i ∈ s, rowNorm1 (f i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rowNorm1]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    linarith [rowNorm1_add_le (f a) (∑ i ∈ s, f i) u, ih]

theorem rowNorm1_smul {Q r : ℕ} (c : ℤ) (A : Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ)
    (u : AuxLabel Q r) :
    rowNorm1 (c • A) u = |c| * rowNorm1 A u := by
  unfold rowNorm1
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  simp [abs_mul]

@[simp]
theorem rowNorm1_one {Q r : ℕ} (u : AuxLabel Q r) :
    rowNorm1 (1 : Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ) u = 1 := by
  unfold rowNorm1
  have h :
      ∀ y : AuxLabel Q r,
        |(1 : Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ) u y| = if y = u then 1 else 0 := by
    intro y
    by_cases hy : y = u
    · subst hy
      simp
    · have hy' : u ≠ y := Ne.symm hy
      simp [hy, hy']
  simp_rw [h]
  simp

@[simp]
theorem rowNorm1_subsetSwapMatrix {Q r : ℕ} (J : Finset (Fin Q)) (u : AuxLabel Q r) :
    rowNorm1 (subsetSwapMatrix Q r ℤ J) u = 1 := by
  unfold rowNorm1 subsetSwapMatrix
  have h :
      ∀ y : AuxLabel Q r,
        |(if y = subsetSwap J u then (1 : ℤ) else 0)| = if y = subsetSwap J u then 1 else 0 := by
    intro y
    split_ifs <;> rfl
  simp_rw [h]
  simp

theorem rowNorm1_mul_le {Q r : ℕ} (A B : Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ)
    (M : ℤ) (hB : ∀ z : AuxLabel Q r, rowNorm1 B z ≤ M) (u : AuxLabel Q r) :
    rowNorm1 (A * B) u ≤ rowNorm1 A u * M := by
  unfold rowNorm1
  calc
    (∑ y : AuxLabel Q r, |(A * B) u y|) ≤
        ∑ y : AuxLabel Q r, ∑ z : AuxLabel Q r, |A u z| * |B z y| := by
      refine sum_le_sum fun y _ => ?_
      rw [Matrix.mul_apply]
      exact (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun z _ => abs_mul _ _))
    _ = ∑ z : AuxLabel Q r, |A u z| * rowNorm1 B z := by
      rw [sum_comm]
      exact sum_congr rfl fun z _ => (mul_sum _ _ _).symm
    _ ≤ ∑ z : AuxLabel Q r, |A u z| * M :=
      sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hB z) (abs_nonneg _)
    _ = rowNorm1 A u * M := (sum_mul _ _ _).symm

theorem rowNorm1_twoW0_le (Q r : ℕ) (u : AuxLabel Q r) :
    rowNorm1 (twoW0 Q r ℤ) u ≤ 2 * (Q : ℤ) := by
  unfold twoW0
  refine (rowNorm1_sum_le univ _ u).trans ?_
  have h1 : ∀ s : Fin Q, rowNorm1 (1 - slotSwapMatrix Q r ℤ s) u ≤ 2 := by
    intro s
    refine (rowNorm1_sub_le 1 (slotSwapMatrix Q r ℤ s) u).trans ?_
    rw [rowNorm1_one, slotSwapMatrix, rowNorm1_subsetSwapMatrix]
    norm_num
  exact (sum_le_sum fun s _ => h1 s).trans (by simp [mul_comm])

theorem rowNorm1_twoW0_sub_smul_le {Q r A₀ a : ℕ} (ha : A₀ + a ≤ Q) (u : AuxLabel Q r) :
    rowNorm1 (twoW0 Q r ℤ - (2 * ((A₀ : ℤ) + a)) • 1) u ≤ 4 * (Q : ℤ) := by
  refine (rowNorm1_sub_le _ _ u).trans ?_
  rw [rowNorm1_smul, rowNorm1_one, mul_one, abs_of_nonneg (by positivity)]
  have h2W := rowNorm1_twoW0_le Q r u
  have haQ : (A₀ : ℤ) + a ≤ Q := by exact_mod_cast ha
  linarith

theorem rowNorm1_fallingProdMatrixInt_le {Q r A₀ j : ℕ} (hj : ∀ a < j, A₀ + a ≤ Q)
    (u : AuxLabel Q r) :
    rowNorm1 (fallingProdMatrixInt Q r A₀ j) u ≤ (4 * (Q : ℤ)) ^ j := by
  unfold fallingProdMatrixInt
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, pow_succ]
    refine (rowNorm1_mul_le _ _ (4 * (Q : ℤ))
      (fun z => rowNorm1_twoW0_sub_smul_le (hj j (Nat.lt_succ_self j)) z) u).trans ?_
    exact mul_le_mul_of_nonneg_right (ih (fun a ha => hj a (Nat.lt_succ_of_lt ha)) u)
      (by positivity)

theorem rowNorm1_fallingTermMatrixInt_le {Q r A₀ j : ℕ} (hj : ∀ a < j, A₀ + a ≤ Q)
    (u : AuxLabel Q r) :
    rowNorm1 (fallingTermMatrixInt Q r A₀ j) u ≤ (4 * (Q : ℤ)) ^ j := by
  unfold fallingTermMatrixInt
  rw [rowNorm1_smul, abs_neg_one_pow, one_mul]
  exact rowNorm1_fallingProdMatrixInt_le hj u

/-- **Lemma 4.6 matrix norm bound (p. 33)**: when `0 < Q` and every interpolation node `A₀ + a`
(`a < R - 1`) is at most `Q`, every row of `M0ScaledInt Q r A₀ R` has `ℓ₁`-norm at most
`(R - 1)! * R * (4 * Q) ^ (R - 1)` (i.e. `‖M_0‖_∞ ≤ R (4 Q)^{R - 1}`). -/
theorem rowNorm1_M0ScaledInt_le {Q r A₀ R : ℕ} (hQ : 0 < Q) (hI : ∀ a < R - 1, A₀ + a ≤ Q)
    (u : AuxLabel Q r) :
    rowNorm1 (M0ScaledInt Q r A₀ R) u ≤
      ((R - 1).factorial : ℤ) * (R : ℤ) * (4 * (Q : ℤ)) ^ (R - 1) := by
  have hswap :
      rowNorm1 (M0ScaledInt Q r A₀ R) u =
        rowNorm1
          (∑ j ∈ range R,
            (((R - 1).factorial / j.factorial : ℕ) : ℤ) • fallingTermMatrixInt Q r A₀ j)
          (fullSwap u) := by
    unfold M0ScaledInt rowNorm1
    refine sum_congr rfl fun y _ => ?_
    rw [fullSwapMatrix_mul_apply]
  rw [hswap]
  refine (rowNorm1_sum_le (range R) _ (fullSwap u)).trans ?_
  have hterm :
      ∀ j ∈ range R,
        rowNorm1 ((((R - 1).factorial / j.factorial : ℕ) : ℤ) • fallingTermMatrixInt Q r A₀ j)
          (fullSwap u) ≤
          ((R - 1).factorial : ℤ) * (4 * (Q : ℤ)) ^ (R - 1) := by
    intro j hj
    have hjle : j ≤ R - 1 := Nat.le_sub_one_of_lt (mem_range.1 hj)
    rw [rowNorm1_smul, abs_of_nonneg (by positivity)]
    have hdiv : (((R - 1).factorial / j.factorial : ℕ) : ℤ) ≤ ((R - 1).factorial : ℤ) := by
      exact_mod_cast Nat.div_le_self (R - 1).factorial j.factorial
    have hfall := rowNorm1_fallingTermMatrixInt_le
      (fun a ha => hI a (ha.trans_le hjle)) (fullSwap u)
    have hpow : (4 * (Q : ℤ)) ^ j ≤ (4 * (Q : ℤ)) ^ (R - 1) :=
      pow_le_pow_right₀ (by omega) hjle
    exact mul_le_mul hdiv (hfall.trans hpow) (rowNorm1_nonneg _ _) (by positivity)
  calc
    (∑ j ∈ range R,
        rowNorm1 ((((R - 1).factorial / j.factorial : ℕ) : ℤ) • fallingTermMatrixInt Q r A₀ j)
          (fullSwap u)) ≤
      ∑ _j ∈ range R, ((R - 1).factorial : ℤ) * (4 * (Q : ℤ)) ^ (R - 1) :=
        sum_le_sum hterm
    _ = ((R - 1).factorial : ℤ) * (R : ℤ) * (4 * (Q : ℤ)) ^ (R - 1) := by
      rw [sum_const, card_range, nsmul_eq_mul]
      ring

/-- **Lemma 4.6 auxiliary row coefficient bound (p. 33)**: when `0 < Q` and every interpolation
node `A₀ + a` (`a < R - 1`) is at most `Q` (`hI : ∀ a < R - 1, A₀ + a ≤ Q`), for every
`u : AuxLabel Q r`, the sum of the absolute values of all coefficients in the cleared row
`auxReplacementRowScaledInt Q r A₀ R u` is at most
`commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (4 * Q) ^ (R - 1))`. -/
theorem sum_coeffNorm1_auxReplacementRowScaledInt_le {Q r A₀ R : ℕ}
    (hQ : 0 < Q) (hI : ∀ a < R - 1, A₀ + a ≤ Q) (u : AuxLabel Q r) :
    (∑ y : AuxLabel Q r, ((auxReplacementRowScaledInt Q r A₀ R u y).coeffNorm1 : ℤ)) ≤
      (commonDenom Q R : ℤ) * (1 + (1 + 2 ^ Q) * (R : ℤ) * (4 * (Q : ℤ)) ^ (R - 1)) := by
  have hterm :
      ∀ y : AuxLabel Q r,
        ((auxReplacementRowScaledInt Q r A₀ R u y).coeffNorm1 : ℤ) ≤
          (if u = y then (commonDenom Q R : ℤ) else 0) +
            (Q.factorial : ℤ) * (1 + 2 ^ Q) * |M0ScaledInt Q r A₀ R u y| := by
    intro y
    unfold auxReplacementRowScaledInt
    refine (natCast_coeffNorm1_add_le _ _).trans ?_
    rw [natCast_coeffNorm1_C, abs_mul, abs_of_nonneg (by positivity)]
    have h1 :
        |(if u = y then ((R - 1).factorial : ℤ) else 0) - M0ScaledInt Q r A₀ R u y| ≤
          (if u = y then ((R - 1).factorial : ℤ) else 0) + |M0ScaledInt Q r A₀ R u y| := by
      refine (abs_sub _ _).trans ?_
      have hite :
          |if u = y then ((R - 1).factorial : ℤ) else 0| =
            if u = y then ((R - 1).factorial : ℤ) else 0 := by
        split_ifs <;> simp [abs_of_nonneg (by positivity : 0 ≤ ((R - 1).factorial : ℤ))]
      rw [hite]
    have h2 :
        ((C (M0ScaledInt Q r A₀ R u y) * mismatchAnnihilatorScaledInt u y).coeffNorm1 : ℤ) ≤
          |M0ScaledInt Q r A₀ R u y| * ((Q.factorial : ℤ) * 2 ^ Q) :=
      (natCast_coeffNorm1_C_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (natCast_coeffNorm1_mismatchAnnihilatorScaledInt_le u y)
          (abs_nonneg _))
    have hcd :
        (Q.factorial : ℤ) * (if u = y then ((R - 1).factorial : ℤ) else 0) =
          if u = y then (commonDenom Q R : ℤ) else 0 := by
      unfold commonDenom
      split_ifs <;> push_cast <;> ring
    calc
      (Q.factorial : ℤ) *
            |(if u = y then ((R - 1).factorial : ℤ) else 0) - M0ScaledInt Q r A₀ R u y| +
          ((C (M0ScaledInt Q r A₀ R u y) * mismatchAnnihilatorScaledInt u y).coeffNorm1 : ℤ) ≤
        (Q.factorial : ℤ) *
            ((if u = y then ((R - 1).factorial : ℤ) else 0) + |M0ScaledInt Q r A₀ R u y|) +
          |M0ScaledInt Q r A₀ R u y| * ((Q.factorial : ℤ) * 2 ^ Q) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
      _ = (if u = y then (commonDenom Q R : ℤ) else 0) +
          (Q.factorial : ℤ) * (1 + 2 ^ Q) * |M0ScaledInt Q r A₀ R u y| := by
        rw [mul_add, hcd]
        ring
  have hQpos_coeff : 0 ≤ (Q.factorial : ℤ) * (1 + 2 ^ Q) :=
    mul_nonneg (by positivity) (by positivity)
  calc
    (∑ y : AuxLabel Q r, ((auxReplacementRowScaledInt Q r A₀ R u y).coeffNorm1 : ℤ)) ≤
        ∑ y : AuxLabel Q r,
          ((if u = y then (commonDenom Q R : ℤ) else 0) +
            (Q.factorial : ℤ) * (1 + 2 ^ Q) * |M0ScaledInt Q r A₀ R u y|) :=
      sum_le_sum fun y _ => hterm y
    _ = (commonDenom Q R : ℤ) +
          (Q.factorial : ℤ) * (1 + 2 ^ Q) * rowNorm1 (M0ScaledInt Q r A₀ R) u := by
      simp only [sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte, ← mul_sum]
      rfl
    _ ≤ (commonDenom Q R : ℤ) +
          (Q.factorial : ℤ) * (1 + 2 ^ Q) *
            (((R - 1).factorial : ℤ) * (R : ℤ) * (4 * (Q : ℤ)) ^ (R - 1)) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left (rowNorm1_M0ScaledInt_le hQ hI u) hQpos_coeff) _
    _ = (commonDenom Q R : ℤ) * (1 + (1 + 2 ^ Q) * (R : ℤ) * (4 * (Q : ℤ)) ^ (R - 1)) := by
      unfold commonDenom
      push_cast
      ring

/-- **Lemma 4.6 original-variable row coefficient bound (p. 33)**: when `0 < Q`, `place` is
injective, and `hI : ∀ a < R - 1, A₀ + a ≤ Q`, the sum of the absolute values of all coefficients in
the cleared row `varReplacementRowScaledInt Q r A₀ R place varOf e` on `Fin n` is at most
`commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (4 * Q) ^ (R - 1))`. -/
theorem sum_coeffNorm1_varReplacementRowScaledInt_le {A : Type*} [Fintype A]
    {Q r A₀ R n h : ℕ} {place : A → Fin h × AuxLabel Q r}
    (hQ : 0 < Q) (hinj : Function.Injective place) (varOf : A → Fin n)
    (hI : ∀ a < R - 1, A₀ + a ≤ Q) (e : A) :
    (∑ v : Fin n, ((varReplacementRowScaledInt Q r A₀ R place varOf e v).coeffNorm1 : ℤ)) ≤
      (commonDenom Q R : ℤ) * (1 + (1 + 2 ^ Q) * (R : ℤ) * (4 * (Q : ℤ)) ^ (R - 1)) := by
  classical
  have htri :
      (∑ v : Fin n, ((varReplacementRowScaledInt Q r A₀ R place varOf e v).coeffNorm1 : ℤ)) ≤
        ∑ v : Fin n,
          ∑ e' ∈ univ.filter (fun e' : A => (place e').1 = (place e).1 ∧ varOf e' = v),
            ((auxReplacementRowScaledInt Q r A₀ R (place e).2 (place e').2).coeffNorm1 : ℤ) :=
    sum_le_sum fun v _ => natCast_coeffNorm1_sum_le _ _
  have hU :
      (∑ v : Fin n,
          ∑ e' ∈ univ.filter (fun e' : A => (place e').1 = (place e).1 ∧ varOf e' = v),
            ((auxReplacementRowScaledInt Q r A₀ R (place e).2 (place e').2).coeffNorm1 : ℤ)) =
        ∑ e' ∈ univ.filter (fun e' : A => (place e').1 = (place e).1),
          ((auxReplacementRowScaledInt Q r A₀ R (place e).2 (place e').2).coeffNorm1 : ℤ) := by
    rw [← sum_biUnion]
    · congr 1
      ext e'
      simp
    · intro v₁ _ v₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro e' h1 h2
      simp only [mem_filter, mem_univ, true_and] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  have hinj_on :
      Set.InjOn (fun e' : A => (place e').2)
        (univ.filter (fun e' : A => (place e').1 = (place e).1)) := by
    intro e₁ he₁ e₂ he₂ h2
    simp only [mem_coe, mem_filter, mem_univ, true_and] at he₁ he₂
    exact hinj (Prod.ext (he₁.trans he₂.symm) h2)
  have himg :
      (∑ e' ∈ univ.filter (fun e' : A => (place e').1 = (place e).1),
          ((auxReplacementRowScaledInt Q r A₀ R (place e).2 (place e').2).coeffNorm1 : ℤ)) =
        ∑ y ∈ (univ.filter (fun e' : A => (place e').1 = (place e).1)).image
            (fun e' : A => (place e').2),
          ((auxReplacementRowScaledInt Q r A₀ R (place e).2 y).coeffNorm1 : ℤ) :=
    (Finset.sum_image
      (f := fun y => ((auxReplacementRowScaledInt Q r A₀ R (place e).2 y).coeffNorm1 : ℤ))
      hinj_on).symm
  have hsub :
      (∑ y ∈ (univ.filter (fun e' : A => (place e').1 = (place e).1)).image
            (fun e' : A => (place e').2),
          ((auxReplacementRowScaledInt Q r A₀ R (place e).2 y).coeffNorm1 : ℤ)) ≤
        ∑ y : AuxLabel Q r, ((auxReplacementRowScaledInt Q r A₀ R (place e).2 y).coeffNorm1 : ℤ) :=
    sum_le_univ_sum_of_nonneg fun y => Nat.cast_nonneg _
  exact htri.trans (by
    rw [hU, himg]
    exact hsub.trans (sum_coeffNorm1_auxReplacementRowScaledInt_le hQ hI (place e).2))

end Cslib.LinearAlgebra
