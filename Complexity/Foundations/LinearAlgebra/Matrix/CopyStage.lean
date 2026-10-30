/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Matrix.FactorialTruncation
import Mathlib.Algebra.BigOperators.Fin

/-!
# One stage of the correction-and-copy hierarchy

One stage of the hierarchy of the OpenAI preprint (2026-09-23), Section 4, ideas 3 and 4 in issue
#474 [OpenAI2026LogSpace], takes a transition matrix `C` with entries at most `f`, corrects it to
`D = C - E + E C` with a finite cutoff correction `E` (`Matrix.cutoffCorrectionIter`), and splits
the remaining large entries of `D` among copies of their targets (`Matrix.copyStage`). This file
proves the deterministic bounds of such a stage. The result `C⁺` has entries at most `f / q`, and
its support lies in a set at most twice as large as the support of `C`
(`Matrix.copyStage_rates`). These are exactly the per-stage hypotheses of the stage bound
`Matrix.sub_rewardTransport_mulVec_le_pow`; `Matrix.sub_rewardTransport_mulVec_le_of_rates`
iterates them.

Stages can be chained. If `C` is strictly upper triangular, so is the residual `D`
(`Matrix.cutoffCorrection_residual_isStrictUpperTriangular`), and the copy step is strictly upper
triangular for the lexicographic order on the copies `Lex (V × Fin (m + 1))`, which is linearly
ordered (`Matrix.copyStage_isStrictUpperTriangular`). Its rows sum to at most one
(`Matrix.copyStage_mulVec_one_le` with `Matrix.correction_mulVec_one_le`) and its entries are
nonnegative under the cutoff assumptions `0 ≤ χ ≤ 1` (`Matrix.copyStage_nonneg` with
`Matrix.cutoffCorrection_residual_nonneg`), so it satisfies the input hypotheses of the next stage.

The choice of which columns are corrected and which vertices get active copies comes from the
preprint's *detectors*, which are probabilistic. Here it is an interface: copy weights `r` with
`r 0 = 1`, and a finite set `O` of *overloaded* vertices, such that

* only overloaded vertices have active extra copies: `r j x ≠ 0 → x ∈ O` for `j ≠ 0`;
* every column is either *fully corrected*, `t - θ₂ f ≤ φ y t` for all `t`, or overloaded with all
  its copies active;
* `m |O| ≤ |A|`, where `m + 1` is the number of copies and `A` covers the support of `C`.

The last condition follows from incidence counting (`Matrix.card_mul_le_of_incidences`): if every
overloaded column has many large entries in one of a few matrices with the stated row-sum bounds,
as the detectors guarantee for the pilot inputs, then there are few overloaded columns. The pilot
inputs have bounded row sums, not necessarily at most one [OpenAI2026LogSpace, Lemma 4.2].

The corrected matrix also satisfies the remaining bounds of Lemma 4.4 of the preprint. Its entries
are at most `(k + 1) f` (`Matrix.cutoffCorrection_residual_le_mul`). It dominates its unsigned
constituents, `θ / (2 (k + 1)) (C + E + E C) ≤ D` (`Matrix.cutoffCorrection_residual_dominates`),
which lets the three terms of `D` be estimated separately. Its support stays within that of `C`
(`Matrix.cutoffCorrection_residual_mem`).

## Main definitions

* `Matrix.copyFraction`: the proportions in which an entry is split among `m + 1` copies.
* `Matrix.copyStage`: the copy step `Matrix.copySplit` with these proportions.
* `Matrix.copyCover`: the copies that can be active, given a cover of the parents.

## Main results

* `Matrix.cutoffCorrectionIter_sum_le`, `Matrix.cutoffCorrectionIter_le_mul`: row sums and
  entries of the iterates.
* `Matrix.cutoffCorrection_residual_le_mul`, `Matrix.cutoffCorrection_residual_dominates`,
  `Matrix.cutoffCorrection_residual_mem`: entry bound, domination and support of the residual.
* `Matrix.copyStage_mul_copyWeight`, `Matrix.copyStage_nonneg`, `Matrix.copyStage_mulVec_one_le`,
  `Matrix.copyStage_le`, `Matrix.copyStage_mem_copyCover`, `Matrix.card_copyCover_le`: the copy
  step intertwines with its projection, is substochastic, has small entries and few active
  copies.
* `Matrix.cutoffCorrection_residual_isStrictUpperTriangular`,
  `Matrix.copyStage_isStrictUpperTriangular`: a stage maps strictly upper triangular matrices to
  strictly upper triangular ones, for the lexicographic order on the copies.
* `Matrix.card_mul_le_of_incidences`: incidence counting.
* `Matrix.copyStage_rates`: the one-stage density and active-count bounds.
* `Matrix.sub_rewardTransport_mulVec_le_of_rates`: the stage bound from per-stage rates.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Lemma 4.2, Lemma 4.4, Proposition 4.5 and Proposition 4.7 (preprint, not peer reviewed)
-/

public section

open Finset

namespace Matrix

/-! ### Residual bounds for cutoff corrections -/

section Residual

variable {V : Type*} [Fintype V] {φ : V → ℝ → ℝ} {C : Matrix V V ℝ} {f θ : ℝ}

variable (hC0 : ∀ x y, 0 ≤ C x y) (hφ0 : ∀ y t, 0 ≤ φ y t)
  (hφθ : ∀ y t, φ y t ≤ max (t - θ * f) 0) (hθf : 0 ≤ θ * f)

omit [Fintype V] in
include hφθ hθf in
private theorem cutoff_le_self' (y : V) {t : ℝ} (ht : 0 ≤ t) : φ y t ≤ t :=
  (hφθ y t).trans (max_le (by linarith) ht)

omit [Fintype V] in
include hφ0 hφθ hθf in
private theorem cutoff_zero (y : V) : φ y 0 = 0 :=
  le_antisymm ((hφθ y 0).trans (max_le (by linarith) le_rfl)) (hφ0 y 0)

include hC0 hφ0 hφθ hθf in
private theorem iter_succ_le_input (k : ℕ) (x y : V) :
    cutoffCorrectionIter φ C (k + 1) x y ≤ (C + cutoffCorrectionIter φ C k * C) x y := by
  rw [cutoffCorrectionIter_succ]
  exact cutoff_le_self' hφθ hθf y <| add_nonneg (hC0 x y) <| Finset.sum_nonneg fun z _ =>
    mul_nonneg (cutoffCorrectionIter_nonneg hφ0 k x z) (hC0 z y)

include hC0 hφ0 hφθ hθf in
/-- **Row sums of the iterates**: the `k`-th iterate of a cutoff correction of a substochastic
`C` has row sums at most `k` [OpenAI2026LogSpace, Lemma 4.2]. -/
theorem cutoffCorrectionIter_sum_le (hC1 : C *ᵥ 1 ≤ 1) (k : ℕ) (x : V) :
    ∑ y, cutoffCorrectionIter φ C k x y ≤ k := by
  have hrow : ∀ z, ∑ y, C z y ≤ 1 := fun z => by simpa [mulVec, dotProduct] using hC1 z
  induction k with
  | zero => simp [cutoffCorrectionIter]
  | succ k ih =>
    set F := cutoffCorrectionIter φ C k
    calc ∑ y, cutoffCorrectionIter φ C (k + 1) x y ≤ ∑ y, (C + F * C) x y :=
          Finset.sum_le_sum fun y _ => iter_succ_le_input hC0 hφ0 hφθ hθf k x y
      _ = ∑ y, C x y + ∑ z, F x z * ∑ y, C z y := by
          simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib, Finset.mul_sum]
          rw [Finset.sum_comm]
      _ ≤ 1 + ∑ z, F x z * 1 := add_le_add (hrow x) (Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (hrow z) (cutoffCorrectionIter_nonneg hφ0 k x z))
      _ ≤ (k + 1 : ℕ) := by simp only [mul_one]; push_cast; linarith

include hC0 hφ0 hφθ hθf in
/-- The input `(C + E_k C) x y` of the `(k + 1)`-th step is at most `(k + 1) f`. -/
private theorem input_le (hCf : ∀ x y, C x y ≤ f) (hf : 0 ≤ f) (hC1 : C *ᵥ 1 ≤ 1) (k : ℕ)
    (x y : V) : (C + cutoffCorrectionIter φ C k * C) x y ≤ (k + 1) * f := by
  have hsum := cutoffCorrectionIter_sum_le hC0 hφ0 hφθ hθf hC1 k x
  calc (C + cutoffCorrectionIter φ C k * C) x y
      = C x y + ∑ z, cutoffCorrectionIter φ C k x z * C z y := rfl
    _ ≤ f + ∑ z, cutoffCorrectionIter φ C k x z * f := add_le_add (hCf x y)
        (Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (hCf z y) (cutoffCorrectionIter_nonneg hφ0 k x z))
    _ ≤ (k + 1) * f := by rw [← Finset.sum_mul]; nlinarith

include hC0 hφ0 hφθ hθf in
/-- **Entries of the iterates**: the `k`-th iterate has entries at most `k f`
[OpenAI2026LogSpace, Lemma 4.2]. -/
theorem cutoffCorrectionIter_le_mul (hCf : ∀ x y, C x y ≤ f) (hf : 0 ≤ f) (hC1 : C *ᵥ 1 ≤ 1)
    (k : ℕ) (x y : V) : cutoffCorrectionIter φ C k x y ≤ k * f := by
  cases k with
  | zero => simp [cutoffCorrectionIter]
  | succ k =>
    push_cast
    exact (iter_succ_le_input hC0 hφ0 hφθ hθf k x y).trans
      (input_le hC0 hφ0 hφθ hθf hCf hf hC1 k x y)

include hC0 hφ0 hφθ hθf in
/-- **The residual entry bound**: `C - E_k + E_k C` has entries at most `(k + 1) f`
[OpenAI2026LogSpace, Lemma 4.4]. -/
theorem cutoffCorrection_residual_le_mul (hCf : ∀ x y, C x y ≤ f) (hf : 0 ≤ f)
    (hC1 : C *ᵥ 1 ≤ 1) (k : ℕ) (x y : V) :
    (C - cutoffCorrectionIter φ C k + cutoffCorrectionIter φ C k * C) x y ≤ (k + 1) * f := by
  have h := input_le hC0 hφ0 hφθ hθf hCf hf hC1 k x y
  have h0 := cutoffCorrectionIter_nonneg (C := C) hφ0 k x y
  simp only [Matrix.add_apply, Matrix.sub_apply] at h ⊢
  linarith

include hC0 hφ0 hφθ hθf in
/-- **Domination of the unsigned terms**: for `θ ≤ 1`, the residual of the `(k + 1)`-th iterate
dominates a fixed multiple of the sum of its unsigned constituents,
`θ / (2 (k + 1)) (C + E + E C) ≤ C - E + E C` [OpenAI2026LogSpace, Lemma 4.4]. -/
theorem cutoffCorrection_residual_dominates (hCf : ∀ x y, C x y ≤ f) (hf : 0 ≤ f)
    (hC1 : C *ᵥ 1 ≤ 1) (hφm : ∀ y, Monotone (φ y)) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (k : ℕ)
    (x y : V) :
    θ / (2 * (k + 1)) * (C + cutoffCorrectionIter φ C (k + 1) +
        cutoffCorrectionIter φ C (k + 1) * C) x y ≤
      (C - cutoffCorrectionIter φ C (k + 1) + cutoffCorrectionIter φ C (k + 1) * C) x y := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have ha0 : 0 ≤ (C + cutoffCorrectionIter φ C k * C) x y :=
    add_nonneg (hC0 x y) (Finset.sum_nonneg fun z _ =>
      mul_nonneg (cutoffCorrectionIter_nonneg hφ0 k x z) (hC0 z y))
  have ha := input_le hC0 hφ0 hφθ hθf hCf hf hC1 k x y
  have hEa : cutoffCorrectionIter φ C (k + 1) x y =
      φ y ((C + cutoffCorrectionIter φ C k * C) x y) := by
    rw [cutoffCorrectionIter_succ]; rfl
  have he0 := cutoffCorrectionIter_nonneg (C := C) hφ0 (k + 1) x y
  have hea := iter_succ_le_input hC0 hφ0 hφθ hθf k x y
  have hFE : (cutoffCorrectionIter φ C k * C) x y ≤ (cutoffCorrectionIter φ C (k + 1) * C) x y :=
    Finset.sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_right (cutoffCorrectionIter_le_succ hC0 hφ0 hφm k x z) (hC0 z y)
  have hθa := hφθ y ((C + cutoffCorrectionIter φ C k * C) x y)
  rw [← hEa] at hθa
  set F := cutoffCorrectionIter φ C k
  set E := cutoffCorrectionIter φ C (k + 1)
  set a := (C + F * C) x y
  set t := θ / (k + 1)
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [div_le_one hk]; linarith
  have hmin : t * a ≤ a - E x y := by
    rcases le_or_gt 0 (a - θ * f) with h | h
    · have he : E x y ≤ a - θ * f := by rw [max_eq_left h] at hθa; exact hθa
      have : t * a ≤ θ * f := by
        calc t * a ≤ t * ((k + 1) * f) := mul_le_mul_of_nonneg_left ha ht0
          _ = θ * f := by simp only [t]; field_simp
      linarith
    · have he : E x y ≤ 0 := by rw [max_eq_right h.le] at hθa; exact hθa
      nlinarith
  have hcoef : θ / (2 * (k + 1)) = t / 2 := by simp only [t]; field_simp
  have h1 : t / 2 * E x y ≤ t / 2 * a := mul_le_mul_of_nonneg_left hea (by positivity)
  have h2 : t / 2 * ((E * C) x y - (F * C) x y) ≤ (E * C) x y - (F * C) x y :=
    mul_le_of_le_one_left (by linarith) (by linarith)
  have hadef : a = C x y + (F * C) x y := rfl
  rw [hcoef]
  simp only [Matrix.add_apply, Matrix.sub_apply]
  nlinarith

variable {A : Finset V}

include hφ0 hφθ hθf in
/-- The iterates are supported within any set `A` covering the support of `C`. -/
theorem cutoffCorrectionIter_mem (hA : ∀ x y, C x y ≠ 0 → x ∈ A ∧ y ∈ A) (k : ℕ) (x y : V)
    (h : cutoffCorrectionIter φ C k x y ≠ 0) : x ∈ A ∧ y ∈ A := by
  induction k generalizing x y with
  | zero => simp [cutoffCorrectionIter] at h
  | succ k ih =>
    by_contra hxy
    apply h
    have hCxy : C x y = 0 := by
      by_contra h'; exact hxy (hA x y h')
    have hin : (C + cutoffCorrectionIter φ C k * C) x y = 0 := by
      simp only [Matrix.add_apply, Matrix.mul_apply, hCxy, zero_add]
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases hE : cutoffCorrectionIter φ C k x z = 0
      · rw [hE, zero_mul]
      by_cases hCz : C z y = 0
      · rw [hCz, mul_zero]
      exact absurd ⟨(ih x z hE).1, (hA z y hCz).2⟩ hxy
    rw [cutoffCorrectionIter_succ]
    change φ y ((C + cutoffCorrectionIter φ C k * C) x y) = 0
    rw [hin, cutoff_zero hφ0 hφθ hθf]

include hφ0 hφθ hθf in
/-- **The residual stays within the support of `C`** [OpenAI2026LogSpace, Lemma 4.4]. -/
theorem cutoffCorrection_residual_mem (hA : ∀ x y, C x y ≠ 0 → x ∈ A ∧ y ∈ A) (k : ℕ)
    (x y : V)
    (h : (C - cutoffCorrectionIter φ C k + cutoffCorrectionIter φ C k * C) x y ≠ 0) :
    x ∈ A ∧ y ∈ A := by
  by_contra hxy
  apply h
  have hE : ∀ u v, cutoffCorrectionIter φ C k u v ≠ 0 → u ∈ A ∧ v ∈ A :=
    cutoffCorrectionIter_mem hφ0 hφθ hθf hA k
  have hCxy : C x y = 0 := by by_contra h'; exact hxy (hA x y h')
  have hExy : cutoffCorrectionIter φ C k x y = 0 := by by_contra h'; exact hxy (hE x y h')
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, hCxy, hExy, sub_zero, zero_add]
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases hEz : cutoffCorrectionIter φ C k x z = 0
  · rw [hEz, zero_mul]
  by_cases hCz : C z y = 0
  · rw [hCz, mul_zero]
  exact absurd ⟨(hE x z hEz).1, (hA z y hCz).2⟩ hxy

include hφ0 hφθ hθf in
/-- The iterates of the cutoff correction of a strictly upper triangular matrix are strictly upper
triangular. -/
theorem cutoffCorrectionIter_isStrictUpperTriangular [Preorder V]
    (hC : C.IsStrictUpperTriangular) (k : ℕ) :
    (cutoffCorrectionIter φ C k).IsStrictUpperTriangular := by
  induction k with
  | zero => intro x y _; simp [cutoffCorrectionIter]
  | succ k ih =>
    intro x y hxy
    rw [cutoffCorrectionIter_succ]
    change φ y ((C + cutoffCorrectionIter φ C k * C) x y) = 0
    rw [(hC.add (ih.mul hC)) hxy, cutoff_zero hφ0 hφθ hθf]

include hφ0 hφθ hθf in
/-- **The residual of a strictly upper triangular matrix is strictly upper triangular.** -/
theorem cutoffCorrection_residual_isStrictUpperTriangular [Preorder V]
    (hC : C.IsStrictUpperTriangular) (k : ℕ) :
    (C - cutoffCorrectionIter φ C k + cutoffCorrectionIter φ C k * C).IsStrictUpperTriangular :=
  have hE := cutoffCorrectionIter_isStrictUpperTriangular hφ0 hφθ hθf hC k
  (hC.sub hE).add (hE.mul hC)

end Residual

/-! ### Copy fractions -/

section Fraction

/-- **Copy fractions** for `m + 1` copies, driven by a cutoff `χ` with values in `[0, 1]`: the
primary copy `0` receives `1 - m / (m + 1) χ t`, every other copy `χ t / (m + 1)`. Small entries
(`χ t = 0`) stay with the primary copy; large ones (`χ t = 1`) are split evenly
[OpenAI2026LogSpace, (4.21)]. -/
@[expose] noncomputable def copyFraction (χ : ℝ → ℝ) (m : ℕ) (t : ℝ) (j : Fin (m + 1)) : ℝ :=
  if j = 0 then 1 - m / (m + 1) * χ t else χ t / (m + 1)

variable {χ : ℝ → ℝ} {m : ℕ} {t : ℝ}

theorem sum_copyFraction (χ : ℝ → ℝ) (m : ℕ) (t : ℝ) : ∑ j, copyFraction χ m t j = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [copyFraction, Fin.succ_ne_zero, ↓reduceIte, Finset.sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem copyFraction_nonneg (h0 : 0 ≤ χ t) (h1 : χ t ≤ 1) (j : Fin (m + 1)) :
    0 ≤ copyFraction χ m t j := by
  have hm : (m : ℝ) / (m + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  unfold copyFraction
  split_ifs
  · nlinarith [mul_le_mul hm h1 h0 zero_le_one]
  · positivity

theorem copyFraction_le_one (h0 : 0 ≤ χ t) (h1 : χ t ≤ 1) (j : Fin (m + 1)) :
    copyFraction χ m t j ≤ 1 := by
  unfold copyFraction
  split_ifs
  · have : 0 ≤ (m : ℝ) / (m + 1) * χ t := by positivity
    linarith
  · rw [div_le_one (by positivity)]; linarith

theorem copyFraction_of_eq_zero (h : χ t = 0) (j : Fin (m + 1)) :
    copyFraction χ m t j = if j = 0 then 1 else 0 := by
  simp [copyFraction, h]

theorem copyFraction_of_eq_one (h : χ t = 1) (j : Fin (m + 1)) :
    copyFraction χ m t j = 1 / (m + 1) := by
  unfold copyFraction
  split_ifs
  · rw [h]; field_simp; ring
  · rw [h]

end Fraction

/-! ### The copy step -/

section Stage

variable {V : Type*} {m : ℕ} {χ : ℝ → ℝ} {τ₀ τ₁ : ℝ} {r : Fin (m + 1) → V → ℝ}
  {D : Matrix V V ℝ}

/-- **The copy step** of the hierarchy: `Matrix.copySplit` with the proportions
`Matrix.copyFraction χ m (D x y)` [OpenAI2026LogSpace, (4.23)]. -/
@[expose] noncomputable def copyStage (χ : ℝ → ℝ) (m : ℕ) (r : Fin (m + 1) → V → ℝ)
    (D : Matrix V V ℝ) : Matrix (V × Fin (m + 1)) (V × Fin (m + 1)) ℝ :=
  copySplit r (fun x y => copyFraction χ m (D x y)) D

/-- The copies that can be active: the primary copies of a cover `A` of the parents, and all
copies of the overloaded vertices `O`. -/
@[expose] def copyCover [DecidableEq V] (A O : Finset V) : Finset (V × Fin (m + 1)) :=
  A ×ˢ {0} ∪ O ×ˢ univ.erase 0

/-- **The copy step stays strictly upper triangular** for the lexicographic order on the copies:
`(x, i)` comes before `(y, j)` when `x < y`, or `x = y` and `i < j`. Indexed by
`Lex (V × Fin (m + 1))`, which is linearly ordered when `V` is, the copy step can be the input of
the next stage (`Matrix.copySplit_isStrictUpperTriangular`). -/
theorem copyStage_isStrictUpperTriangular [LT V] (hD : D.IsStrictUpperTriangular) :
    ((copyStage χ m r D).submatrix ofLex ofLex).IsStrictUpperTriangular :=
  copySplit_isStrictUpperTriangular hD

theorem card_copyCover_le [DecidableEq V] (A O : Finset V) :
    #(copyCover (m := m) A O) ≤ #A + m * #O := by
  refine (card_union_le _ _).trans ?_
  rw [card_product, card_product, card_singleton, card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin, mul_one, Nat.add_sub_cancel, mul_comm]

/-- **The copy step intertwines with its projection** when the primary weight is one and every
large entry `τ₀ < D x y` has all copies of its target active [OpenAI2026LogSpace, (4.26)]. -/
theorem copyStage_mul_copyWeight [Fintype V] [DecidableEq V] (hr0 : ∀ x, r 0 x = 1)
    (hχ₀ : ∀ t, t ≤ τ₀ → χ t = 0)
    (hbig : ∀ x y, τ₀ < D x y → ∀ j, r j y = 1) :
    copyStage χ m r D * copyWeight r = copyWeight r * D := by
  refine copySplit_mul_copyWeight fun x y _ => ?_
  rcases le_or_gt (D x y) τ₀ with h | h
  · rw [Fin.sum_univ_succ]
    simp [copyFraction_of_eq_zero (hχ₀ _ h), Fin.succ_ne_zero, hr0]
  · simp only [hbig x y h, mul_one]
    exact sum_copyFraction χ m (D x y)

theorem copyStage_nonneg (hr : ∀ j x, 0 ≤ r j x) (hD : ∀ x y, 0 ≤ D x y)
    (hχ0 : ∀ t, 0 ≤ χ t) (hχ1 : ∀ t, χ t ≤ 1) (a b : V × Fin (m + 1)) :
    0 ≤ copyStage χ m r D a b :=
  copySplit_nonneg hr (fun _ _ j => copyFraction_nonneg (hχ0 _) (hχ1 _) j) hD a b

/-- **The copy step preserves the row-sum upper bound**: its rows sum to at most one when `D` is
nonnegative with rows summing to at most one and the weights lie in `[0, 1]`. Substochasticity
also needs nonnegative entries, which `Matrix.copyStage_nonneg` gives under the additional
cutoff assumptions `0 ≤ χ ≤ 1`. -/
theorem copyStage_mulVec_one_le [Fintype V] (hr0 : ∀ j x, 0 ≤ r j x) (hr1 : ∀ j x, r j x ≤ 1)
    (hD0 : ∀ x y, 0 ≤ D x y) (hD1 : D *ᵥ 1 ≤ 1) : copyStage χ m r D *ᵥ 1 ≤ 1 :=
  copySplit_mulVec_one_le hr0 hr1 (fun x y => (sum_copyFraction χ m (D x y)).le) hD0 hD1

/-- **The density bound**: if the entries of `D` are at most `K`, the cutoff is one from `τ₁`
on, `τ₁ ≤ b` and `K / (m + 1) ≤ b`, the copy step has entries at most `b`
[OpenAI2026LogSpace, Proposition 4.5]. -/
theorem copyStage_le (hr0 : ∀ j x, 0 ≤ r j x) (hr1 : ∀ j x, r j x ≤ 1)
    (hD0 : ∀ x y, 0 ≤ D x y) {K b : ℝ} (hDK : ∀ x y, D x y ≤ K) (hχ0 : ∀ t, 0 ≤ χ t)
    (hχ1 : ∀ t, χ t ≤ 1) (hχ₁ : ∀ t, τ₁ ≤ t → χ t = 1) (hτ₁ : τ₁ ≤ b)
    (hK : K / (m + 1) ≤ b) (a c : V × Fin (m + 1)) : copyStage χ m r D a c ≤ b := by
  simp only [copyStage, copySplit, of_apply]
  have hrD : r a.2 a.1 * D a.1 c.1 ≤ D a.1 c.1 :=
    mul_le_of_le_one_left (hD0 _ _) (hr1 _ _)
  have hrD0 : 0 ≤ r a.2 a.1 * D a.1 c.1 := mul_nonneg (hr0 _ _) (hD0 _ _)
  rcases lt_or_ge (D a.1 c.1) τ₁ with h | h
  · calc r a.2 a.1 * D a.1 c.1 * copyFraction χ m (D a.1 c.1) c.2
        ≤ r a.2 a.1 * D a.1 c.1 :=
          mul_le_of_le_one_right hrD0 (copyFraction_le_one (hχ0 _) (hχ1 _) _)
      _ ≤ b := by linarith
  · rw [copyFraction_of_eq_one (hχ₁ _ h)]
    calc r a.2 a.1 * D a.1 c.1 * (1 / (m + 1)) ≤ K * (1 / (m + 1)) :=
          mul_le_mul_of_nonneg_right (hrD.trans (hDK _ _)) (by positivity)
      _ ≤ b := by rw [mul_one_div]; exact hK

/-- **Active copies**: if `A` covers the support of `D`, extra copies of `x` are active only for
overloaded `x`, and large entries have overloaded targets, then the copy step is supported in
`Matrix.copyCover A O` [OpenAI2026LogSpace, Proposition 4.5]. -/
theorem copyStage_mem_copyCover [DecidableEq V] {A O : Finset V}
    (hA : ∀ x y, D x y ≠ 0 → x ∈ A ∧ y ∈ A)
    (hrO : ∀ j x, j ≠ 0 → r j x ≠ 0 → x ∈ O) (hχ₀ : ∀ t, t ≤ τ₀ → χ t = 0)
    (hcolO : ∀ x y, τ₀ < D x y → y ∈ O) (a b : V × Fin (m + 1))
    (h : copyStage χ m r D a b ≠ 0) : a ∈ copyCover A O ∧ b ∈ copyCover A O := by
  obtain ⟨⟨x, i⟩, ⟨y, j⟩⟩ := (⟨a, b⟩ : _ × _)
  simp only [copyStage, copySplit, of_apply, ne_eq, mul_eq_zero, not_or] at h
  obtain ⟨⟨hr, hD⟩, hs⟩ := h
  have hxy := hA _ _ hD
  simp only [copyCover, mem_union, mem_product, mem_singleton, mem_erase, mem_univ, and_true]
  constructor
  · by_cases hi : a.2 = 0
    · exact Or.inl ⟨hxy.1, hi⟩
    · exact Or.inr ⟨hrO _ _ hi hr, hi⟩
  · by_cases hj : b.2 = 0
    · exact Or.inl ⟨hxy.2, hj⟩
    · refine Or.inr ⟨hcolO a.1 b.1 ?_, hj⟩
      by_contra hle
      exact hs (by simp [copyFraction_of_eq_zero (hχ₀ _ (not_lt.mp hle)), hj])

end Stage

/-! ### Incidence counting -/

/-- **Incidence counting.** Let `G i` be nonnegative matrices whose rows sum to at most `s i` and
vanish outside `A`. If each vertex of `O` is the target of at least `N` entries larger than `δ`
in one of the `G i`, then `|O| N δ ≤ |A| ∑ s i`. With the pilot inputs of the preprint as `G i`,
this bounds the number of overloaded columns [OpenAI2026LogSpace, Proposition 4.5]. -/
theorem card_mul_le_of_incidences {V : Type*} [Fintype V] {k : ℕ}
    (G : Fin k → Matrix V V ℝ) (hG0 : ∀ i x y, 0 ≤ G i x y) (s : Fin k → ℝ)
    (hGs : ∀ i x, ∑ y, G i x y ≤ s i) (A : Finset V) (hGA : ∀ i x y, G i x y ≠ 0 → x ∈ A)
    {δ : ℝ} (hδ : 0 < δ) (O : Finset V) {N : ℕ}
    (hO : ∀ y ∈ O, ∃ i, N ≤ #{x | δ < G i x y}) :
    (#O * N : ℝ) * δ ≤ #A * ∑ i, s i := by
  classical
  -- the indicator of a large entry, scaled by `δ`, is at most the entry
  have hind : ∀ i x y, (if δ < G i x y then δ else 0) ≤ G i x y := fun i x y => by
    split_ifs with h
    · exact h.le
    · exact hG0 i x y
  have hcount : ∀ i y, (#{x | δ < G i x y} : ℝ) * δ = ∑ x, if δ < G i x y then δ else 0 :=
    fun i y => by rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul]
  have hrowA : ∀ i x, (∑ y, if δ < G i x y then δ else 0) ≤ if x ∈ A then s i else 0 := by
    intro i x
    split_ifs with hx
    · exact (Finset.sum_le_sum fun y _ => hind i x y).trans (hGs i x)
    · refine le_of_eq (Finset.sum_eq_zero fun y _ => ?_)
      have : G i x y = 0 := by by_contra h; exact hx (hGA i x y h)
      simp [this, not_lt.mpr hδ.le]
  calc (#O * N : ℝ) * δ = ∑ y ∈ O, (N : ℝ) * δ := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ ∑ y ∈ O, ∑ i, ∑ x, if δ < G i x y then δ else 0 := by
        refine Finset.sum_le_sum fun y hy => ?_
        obtain ⟨i, hi⟩ := hO y hy
        calc (N : ℝ) * δ ≤ (#{x | δ < G i x y} : ℝ) * δ :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hδ.le
          _ = ∑ x, if δ < G i x y then δ else 0 := hcount i y
          _ ≤ ∑ i, ∑ x, if δ < G i x y then δ else 0 :=
              Finset.single_le_sum (f := fun i => ∑ x, if δ < G i x y then δ else 0)
                (fun i _ => Finset.sum_nonneg fun x _ => by split_ifs <;> linarith) (mem_univ i)
    _ ≤ ∑ y, ∑ i, ∑ x, if δ < G i x y then δ else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ O) fun y _ _ =>
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun x _ => by split_ifs <;> linarith
    _ = ∑ i, ∑ x, ∑ y, if δ < G i x y then δ else 0 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ ≤ ∑ i, ∑ x, if x ∈ A then s i else 0 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun x _ => hrowA i x
    _ = #A * ∑ i, s i := by
        simp only [Finset.sum_ite_mem, univ_inter, Finset.sum_const, nsmul_eq_mul]
        rw [Finset.mul_sum]

/-! ### One stage -/

section Rates

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {φ : V → ℝ → ℝ}
  {C : Matrix V V ℝ} {f θ L : ℝ} {m : ℕ} {χ : ℝ → ℝ} {τ₀ τ₁ : ℝ} {r : Fin (m + 1) → V → ℝ}

/-- **One stage of the hierarchy.** Correct `C` by the `k`-th cutoff iterate and split the residual
`D` by `Matrix.copyStage`. Suppose every column is either fully corrected (its cutoff leaves at most
`θ₂ f`) or overloaded with all copies active, the truncation error keeps fully corrected entries
at most `τ₀`, the cutoff `χ` is `0` up to `τ₀` and `1` from `τ₁ ≤ f / q`, there are enough copies
(`(k + 1) f / (m + 1) ≤ f / q`), and `m |O| ≤ |A|` for a cover `A` of the support of `C`. Then
the copy step has entries at most `f / q`, intertwines with its projection, and is supported in a
set of at most `2 |A|` copies [OpenAI2026LogSpace, Proposition 4.5]. -/
theorem copyStage_rates (hC : C.IsStrictUpperTriangular) (hC0 : ∀ x y, 0 ≤ C x y)
    (hCf : ∀ x y, C x y ≤ f) (hC1 : C *ᵥ 1 ≤ 1) (hφ0 : ∀ y t, 0 ≤ φ y t)
    (hφθ : ∀ y t, φ y t ≤ max (t - θ * f) 0) (hφm : ∀ y, Monotone (φ y))
    (hφL : ∀ y s t, s ≤ t → φ y t - φ y s ≤ L * (t - s)) (hf : 0 < f) (hθ : 0 < θ)
    (hL : 0 ≤ L) (k : ℕ) {A O : Finset V} (hA : ∀ x y, C x y ≠ 0 → x ∈ A ∧ y ∈ A)
    (hr0 : ∀ x, r 0 x = 1) (hr01 : ∀ j x, 0 ≤ r j x ∧ r j x ≤ 1)
    (hrO : ∀ j x, j ≠ 0 → r j x ≠ 0 → x ∈ O) {θ₂ : ℝ}
    (hcol : ∀ y, (∀ t, t - θ₂ * f ≤ φ y t) ∨ ((∀ j, r j y = 1) ∧ y ∈ O))
    (hτ₀ : θ₂ * f + f * Real.exp (1 / θ) * (L / θ) ^ k / k.factorial ≤ τ₀)
    (hχ0 : ∀ t, 0 ≤ χ t) (hχ1 : ∀ t, χ t ≤ 1) (hχ₀ : ∀ t, t ≤ τ₀ → χ t = 0)
    (hχ₁ : ∀ t, τ₁ ≤ t → χ t = 1) {q : ℝ} (hτ₁ : τ₁ ≤ f / q)
    (hK : (k + 1) * f / (m + 1) ≤ f / q) (hO : m * #O ≤ #A) :
    let D := C - cutoffCorrectionIter φ C k + cutoffCorrectionIter φ C k * C
    (∀ a b, copyStage χ m r D a b ≤ f / q) ∧
      copyStage χ m r D * copyWeight r = copyWeight r * D ∧
      (∀ a b, copyStage χ m r D a b ≠ 0 →
        a ∈ copyCover A O ∧ b ∈ copyCover A O) ∧
      #(copyCover (m := m) A O) ≤ 2 * #A := by
  intro D
  have hθf : 0 ≤ θ * f := by positivity
  have hD0 : ∀ x y, 0 ≤ D x y := cutoffCorrection_residual_nonneg hC0 hφ0 hφθ hφm hθf k
  have hbig : ∀ x y, τ₀ < D x y → (∀ j, r j y = 1) ∧ y ∈ O := fun x y h => by
    rcases hcol y with hgood | hcopy
    · have := cutoffCorrection_residual_le hC hC0 hCf hC1 hφ0 hφθ hφm hφL hf hθ hL hgood k x
      exact absurd (this.trans hτ₀) (not_le.mpr h)
    · exact hcopy
  refine ⟨copyStage_le (fun j x => (hr01 j x).1) (fun j x => (hr01 j x).2) hD0
      (cutoffCorrection_residual_le_mul hC0 hφ0 hφθ hθf hCf hf.le hC1 k) hχ0 hχ1 hχ₁ hτ₁ hK,
    copyStage_mul_copyWeight hr0 hχ₀ fun x y h => (hbig x y h).1,
    copyStage_mem_copyCover (cutoffCorrection_residual_mem hφ0 hφθ hθf hA k) hrO hχ₀
      fun x y h => (hbig x y h).2, ?_⟩
  exact (card_copyCover_le A O).trans (by omega)

end Rates

/-! ### Iterating the stages -/

section Hierarchy

variable {V : ℕ → Type*} [∀ l, Fintype (V l)] [∀ l, DecidableEq (V l)]
  {C E : ∀ l, Matrix (V l) (V l) ℝ} {P : ∀ l, Matrix (V (l + 1)) (V l) ℝ}

/-- **The stage bound from per-stage rates.** If the entries of `C 0` are at most one, each stage
divides the entry bound by `q = 2 ^ (c + 1)`, and each stage at most doubles a cover of the
support, then along primary copies `0 ≤ p (z 0) - W l (z l) ≤ n * (2 ^ c)⁻¹ ^ l`, where `n`
bounds the initial cover. `Matrix.copyStage_rates` provides the per-stage rates
[OpenAI2026LogSpace, Proposition 4.7]. -/
theorem sub_rewardTransport_mulVec_le_of_rates (hP : ∀ l i j, 0 ≤ P l i j)
    (hP1 : ∀ l, P l *ᵥ 1 ≤ 1) (hC : ∀ l i j, 0 ≤ C l i j)
    (hstep : ∀ l, C (l + 1) * P l = P l * (C l - E l + E l * C l)) {p e : V 0 → ℝ}
    (hp : (1 - C 0) *ᵥ p = e) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {z : ∀ l, V l}
    (hz : ∀ l w, P l (z (l + 1)) w = if w = z l then 1 else 0) {c n : ℕ}
    (hε0 : ∀ x y, C 0 x y ≤ 1)
    (hεs : ∀ l, (∀ x y, C l x y ≤ ((2 : ℝ) ^ (c + 1))⁻¹ ^ l) →
      ∀ x y, C (l + 1) x y ≤ ((2 : ℝ) ^ (c + 1))⁻¹ ^ (l + 1))
    (A : ∀ l, Finset (V l)) (hA : ∀ l x y, C l x y ≠ 0 → y ∈ A l) (hA0 : #(A 0) ≤ n)
    (hAs : ∀ l, #(A (l + 1)) ≤ 2 * #(A l)) (l : ℕ) :
    0 ≤ p (z 0) - (rewardTransport P E l *ᵥ e) (z l) ∧
      p (z 0) - (rewardTransport P E l *ᵥ e) (z l) ≤ n * ((2 : ℝ) ^ c)⁻¹ ^ l := by
  have hε : ∀ l x y, C l x y ≤ ((2 : ℝ) ^ (c + 1))⁻¹ ^ l := by
    intro l
    induction l with
    | zero => simpa using hε0
    | succ l ih => exact hεs l ih
  have hAn : ∀ l, #(A l) ≤ 2 ^ l * n := by
    intro l
    induction l with
    | zero => simpa using hA0
    | succ l ih => rw [pow_succ]; linarith [hAs l]
  exact sub_rewardTransport_mulVec_le_pow hP hP1 hC hstep hp hp0 hp1 hz hε A hA hAn l

end Hierarchy

end Matrix
