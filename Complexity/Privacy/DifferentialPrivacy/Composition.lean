/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Privacy.DifferentialPrivacy.Basic

/-!
# Composition of differentially private mechanisms

Running a `(ε₁, δ₁)`-private mechanism and then a mechanism chosen from its output, which is
`(ε₂, δ₂)`-private for each choice, and releasing both outputs, is `(ε₁ + ε₂, δ₁ + δ₂)`-private
(`DifferentiallyPrivate.bind_pair`) [DworkRoth2014, Theorem B.1]. The source states the case
`ε₁ = ε₂`, `δ₁ = δ₂`; its proof, followed here, bounds the second-stage probability by
`min 1 (exp ε₂ · Pr[…]) + δ₂` and applies the first-stage guarantee to the `[0, 1]`-valued
function `min 1 (exp ε₂ · Pr[…])`. Releasing two independent
mechanisms (`DifferentiallyPrivate.prod`) is the non-adaptive special case
[DworkRoth2014, Theorem 3.16].

`adaptiveComposition M k` runs `k` rounds; round `i` runs `M history`, where `history` lists the
outputs of the previous rounds, most recent first. If every round with `i` previous outputs is
`(ε i, δ i)`-private, the whole transcript is `(∑ i < k, ε i, ∑ i < k, δ i)`-private
(`DifferentiallyPrivate.adaptiveComposition`) [DworkRoth2014, Corollary B.2]. The source fixes
one pair `(ε, δ)` for every round; here the parameters may depend on the round. A mechanism
that ignores its history gives non-adaptive `k`-fold composition.

## Main definitions

* `Cslib.Privacy.adaptiveComposition`: `k` rounds of adaptively chosen mechanisms.

## Main results

* `Cslib.Privacy.DifferentiallyPrivate.bind_pair`: adaptive composition of two mechanisms.
* `Cslib.Privacy.DifferentiallyPrivate.prod`: composition of two independent mechanisms.
* `Cslib.Privacy.DifferentiallyPrivate.adaptiveComposition`: `k`-fold adaptive composition.

## References

* [DworkRoth2014]
-/

open scoped ENNReal
open Cslib.Probability.PMF (monad_bind_eq_bind monad_pure_eq_pure)

public section

namespace Cslib.Privacy

universe u v

namespace DifferentiallyPrivate

variable {D : Type u} {R₁ R₂ : Type v} {Adj : D → D → Prop} {ε₁ ε₂ : ℝ} {δ₁ δ₂ : ℝ≥0∞}

/-- Adaptive composition when the second stage is private only after first-stage outputs
satisfying `P`, and the first stage produces only such outputs. -/
theorem bind_pair_of_support {M₁ : D → PMF R₁} {M₂ : R₁ → D → PMF R₂}
    (h₁ : DifferentiallyPrivate Adj M₁ ε₁ δ₁) (P : R₁ → Prop)
    (hP : ∀ x r₁, r₁ ∈ (M₁ x).support → P r₁)
    (h₂ : ∀ r₁, P r₁ → DifferentiallyPrivate Adj (M₂ r₁) ε₂ δ₂) :
    DifferentiallyPrivate Adj
      (fun x => do
        let r₁ ← M₁ x
        let r₂ ← M₂ r₁ x
        return (r₁, r₂)) (ε₁ + ε₂) (δ₁ + δ₂) := by
  intro x y hxy S
  set c₁ := ENNReal.ofReal (Real.exp ε₁)
  set c₂ := ENNReal.ofReal (Real.exp ε₂)
  have hsec (z : D) (r₁ : R₁) :
      ((M₂ r₁ z).bind fun r₂ => PMF.pure (r₁, r₂)).toOuterMeasure S =
        (M₂ r₁ z).toOuterMeasure (Prod.mk r₁ ⁻¹' S) := by
    rw [← PMF.toOuterMeasure_map_apply]
    rfl
  change ((M₁ x).bind fun r₁ => (M₂ r₁ x).bind fun r₂ => PMF.pure (r₁, r₂)).toOuterMeasure S ≤
    ENNReal.ofReal (Real.exp (ε₁ + ε₂)) *
      ((M₁ y).bind fun r₁ => (M₂ r₁ y).bind fun r₂ => PMF.pure (r₁, r₂)).toOuterMeasure S +
      (δ₁ + δ₂)
  simp only [PMF.toOuterMeasure_bind_apply, hsec]
  set A : R₁ → ℝ≥0∞ := fun r₁ => (M₂ r₁ x).toOuterMeasure (Prod.mk r₁ ⁻¹' S)
  set B : R₁ → ℝ≥0∞ := fun r₁ => (M₂ r₁ y).toOuterMeasure (Prod.mk r₁ ⁻¹' S)
  have hA (r₁ : R₁) : M₁ x r₁ * A r₁ ≤ M₁ x r₁ * (min 1 (c₂ * B r₁) + δ₂) := by
    by_cases h0 : M₁ x r₁ = 0
    · simp [h0]
    gcongr
    rcases le_total 1 (c₂ * B r₁) with hle | hle
    · rw [min_eq_left hle]
      exact (Probability.PMF.toOuterMeasure_le_one _ _).trans le_self_add
    · rw [min_eq_right hle]
      exact h₂ r₁ (hP x r₁ h0) hxy _
  calc ∑' r₁, M₁ x r₁ * A r₁
      ≤ ∑' r₁, (M₁ x r₁ * min 1 (c₂ * B r₁) + M₁ x r₁ * δ₂) := by
        refine tsum_le_tsum fun r₁ => ?_
        rw [← mul_add]
        exact hA r₁
    _ = ∑' r₁, M₁ x r₁ * min 1 (c₂ * B r₁) + δ₂ := by
        rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ c₁ * ∑' r₁, M₁ y r₁ * min 1 (c₂ * B r₁) + δ₁ + δ₂ := by
        gcongr
        exact h₁.tsum_mul_le hxy fun _ => min_le_left _ _
    _ ≤ c₁ * ∑' r₁, M₁ y r₁ * (c₂ * B r₁) + δ₁ + δ₂ := by
        gcongr with r₁
        exact min_le_right _ _
    _ = ENNReal.ofReal (Real.exp (ε₁ + ε₂)) * ∑' r₁, M₁ y r₁ * B r₁ + (δ₁ + δ₂) := by
        rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, add_assoc]
        congr 1
        simp only [mul_left_comm _ c₂, ENNReal.tsum_mul_left, c₁, c₂, mul_assoc]

/-- Adaptive composition: if `M₁` is `(ε₁, δ₁)`-private and `M₂ r₁` is `(ε₂, δ₂)`-private for
every first output `r₁`, then releasing both outputs is `(ε₁ + ε₂, δ₁ + δ₂)`-private
[DworkRoth2014, Theorem B.1]. -/
theorem bind_pair {M₁ : D → PMF R₁} {M₂ : R₁ → D → PMF R₂}
    (h₁ : DifferentiallyPrivate Adj M₁ ε₁ δ₁)
    (h₂ : ∀ r₁, DifferentiallyPrivate Adj (M₂ r₁) ε₂ δ₂) :
    DifferentiallyPrivate Adj
      (fun x => do
        let r₁ ← M₁ x
        let r₂ ← M₂ r₁ x
        return (r₁, r₂)) (ε₁ + ε₂) (δ₁ + δ₂) :=
  bind_pair_of_support h₁ (fun _ => True) (fun _ _ _ => trivial) fun r₁ _ => h₂ r₁

/-- Releasing the outputs of two independent mechanisms, which are `(ε₁, δ₁)`- and
`(ε₂, δ₂)`-private, is `(ε₁ + ε₂, δ₁ + δ₂)`-private [DworkRoth2014, Theorem 3.16]. -/
theorem prod {M₁ : D → PMF R₁} {M₂ : D → PMF R₂}
    (h₁ : DifferentiallyPrivate Adj M₁ ε₁ δ₁) (h₂ : DifferentiallyPrivate Adj M₂ ε₂ δ₂) :
    DifferentiallyPrivate Adj
      (fun x => do
        let r₁ ← M₁ x
        let r₂ ← M₂ x
        return (r₁, r₂)) (ε₁ + ε₂) (δ₁ + δ₂) :=
  bind_pair (M₂ := fun _ => M₂) h₁ fun _ => h₂

end DifferentiallyPrivate

variable {D : Type u} {R : Type v}

/-- `k` rounds of adaptive composition. Round `i` runs `M history`, where `history` lists the
outputs of the previous `i` rounds with the most recent first; the result lists all `k` outputs
in the same order. -/
noncomputable def adaptiveComposition (M : List R → D → PMF R) : ℕ → D → PMF (List R)
  | 0, _ => PMF.pure []
  | k + 1, x => do
    let history ← adaptiveComposition M k x
    let r ← M history x
    return r :: history

/-- Every transcript of `k` rounds lists `k` outputs. -/
theorem length_of_mem_support_adaptiveComposition (M : List R → D → PMF R) (k : ℕ) (x : D)
    {l : List R} (hl : l ∈ (adaptiveComposition M k x).support) : l.length = k := by
  induction k generalizing l with
  | zero =>
    simp only [adaptiveComposition, PMF.support_pure, Set.mem_singleton_iff] at hl
    simp [hl]
  | succ k ih =>
    change l ∈ ((adaptiveComposition M k x).bind fun history =>
      (M history x).bind fun r => PMF.pure (r :: history)).support at hl
    simp only [PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hl
    obtain ⟨history, hhist, r, -, rfl⟩ := hl
    simp [ih hhist]

/-- `k`-fold adaptive composition: if the mechanism run after `i` previous rounds is
`(ε i, δ i)`-private for every history, then the transcript of `k` rounds is
`(∑ i < k, ε i, ∑ i < k, δ i)`-private [DworkRoth2014, Corollary B.2]. -/
theorem DifferentiallyPrivate.adaptiveComposition {Adj : D → D → Prop} {M : List R → D → PMF R}
    {ε : ℕ → ℝ} {δ : ℕ → ℝ≥0∞}
    (h : ∀ history : List R,
      DifferentiallyPrivate Adj (M history) (ε history.length) (δ history.length)) (k : ℕ) :
    DifferentiallyPrivate Adj (Privacy.adaptiveComposition M k)
      (∑ i ∈ Finset.range k, ε i) (∑ i ∈ Finset.range k, δ i) := by
  induction k with
  | zero =>
    intro x y _ S
    simp only [Finset.range_zero, Finset.sum_empty, Real.exp_zero, ENNReal.ofReal_one, one_mul,
      add_zero]
    rfl
  | succ k ih =>
    have hpair := ih.bind_pair_of_support (M₂ := M) (fun history => history.length = k)
      (fun x _ hl => length_of_mem_support_adaptiveComposition M k x hl)
      (fun history hl => hl ▸ h history)
    have hmap := hpair.map fun p => p.2 :: p.1
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    convert hmap using 2 with x
    change ((Privacy.adaptiveComposition M k x).bind fun history =>
      (M history x).bind fun r => PMF.pure (r :: history)) = _
    simp only [monad_bind_eq_bind, monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]

end Cslib.Privacy
