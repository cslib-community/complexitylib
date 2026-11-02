/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate (addition to `Cslib/Probability/StatisticalDistance.lean`)

public import Cslib.Probability.StatisticalDistance
public import Complexity.Probability.PMF
public import Complexity.Probability.StatisticalDistance
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Map

/-!
# The coupling inequality and approximate couplings

Two functions of one sample are at statistical distance at most the probability that they differ
(`Cslib.Probability.PMF.dist_map_map_le`). The sample space may be infinite; only the common
codomain is finite.

This module also defines `Cslib.Probability.PMF.CoupledWithin μ ν ε`, stating that two discrete
distributions `μ, ν : PMF α` admit a joint coupling `ω : PMF (α × α)` whose disagreement
probability `ω.toOuterMeasure {p | p.1 ≠ p.2}` is at most `ε`, together with composition
combinators (`refl`, `symm`, `mono`, `zero_iff`, `map`, `map₂`, `bind_of_eq_on`) and event,
statistical-distance (`dist_le`), and total-variation-distance (`tvDist_le`) bounds.

## Main definitions

* `Cslib.Probability.PMF.CoupledWithin`: coupling of two `PMF`s within disagreement probability
  `ε : ℝ≥0∞`.

## Main results

* `Cslib.Probability.PMF.dist_map_map_le`: the coupling inequality for two maps of a single sample.
* `Cslib.Probability.PMF.CoupledWithin.toOuterMeasure_le`,
  `Cslib.Probability.PMF.CoupledWithin.dist_le`,
  `Cslib.Probability.PMF.CoupledWithin.tvDist_le`: event-probability, statistical-distance, and
  total-variation-distance bounds from a coupling.
-/

public section

open MeasureTheory
open scoped ENNReal Cslib.Probability.PMF

namespace Cslib.Probability.PMF

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

private theorem dist_map_map_le_of_finite [Finite α] [Fintype β] (p : PMF α) (f g : α → β) :
    dist (p.map f) (p.map g) ≤ (p.toOuterMeasure {a | f a ≠ g a}).toReal := by
  classical
  have := Fintype.ofFinite α
  have hmap (h : α → β) :
      (p.bind fun a => (PMF.pure (h a)).map (a, ·)).map Prod.snd = p.map h := by
    simp only [PMF.map_bind, PMF.pure_map]
    rfl
  rw [← hmap f, ← hmap g]
  refine (dist_map_le _ _ Prod.snd).trans ?_
  rw [dist_bind_pair, toOuterMeasure_apply_toReal]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases h : f a = g a
  · simp [h]
  · simpa [h] using mul_le_mul_of_nonneg_left
      (dist_le_one (PMF.pure (f a)) (PMF.pure (g a))) (ENNReal.toReal_nonneg (a := p a))

/-- **Coupling inequality.** Two functions of the same sample are at statistical distance at most
the probability that they differ. -/
theorem dist_map_map_le [Fintype β] (p : PMF α) (f g : α → β) :
    dist (p.map f) (p.map g) ≤ (p.toOuterMeasure {a | f a ≠ g a}).toReal := by
  have h := dist_map_map_le_of_finite (p.map fun a => (f a, g a)) Prod.fst Prod.snd
  rwa [PMF.map_comp, PMF.map_comp, PMF.toOuterMeasure_map_apply] at h

/-- Two discrete distributions `μ, ν : PMF α` are *coupled within* `ε : ℝ≥0∞` if there exists a
joint distribution `ω : PMF (α × α)` with marginals `μ` and `ν` whose disagreement probability
`ω.toOuterMeasure {p | p.1 ≠ p.2}` is at most `ε`. -/
@[expose] def CoupledWithin (μ ν : PMF α) (ε : ℝ≥0∞) : Prop :=
  ∃ ω : PMF (α × α),
    ω.map Prod.fst = μ ∧
    ω.map Prod.snd = ν ∧
    ω.toOuterMeasure {p : α × α | p.1 ≠ p.2} ≤ ε

namespace CoupledWithin

/-- Every distribution is coupled with itself within `0`. -/
theorem refl (μ : PMF α) : CoupledWithin μ μ 0 := by
  refine ⟨μ.map (fun a => (a, a)), ?_, ?_, ?_⟩
  · exact (PMF.map_comp _ _ _).trans (PMF.map_id _)
  · exact (PMF.map_comp _ _ _).trans (PMF.map_id _)
  · refine nonpos_iff_eq_zero.mpr ?_
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    rintro ⟨a₁, a₂⟩ hmem hne
    obtain ⟨a, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
    exact hne ((congrArg Prod.fst heq).symm.trans (congrArg Prod.snd heq))

/-- Symmetry of `CoupledWithin`. -/
theorem symm {μ ν : PMF α} {ε : ℝ≥0∞} (h : CoupledWithin μ ν ε) :
    CoupledWithin ν μ ε := by
  obtain ⟨ω, rfl, rfl, hω⟩ := h
  refine ⟨ω.map Prod.swap, ?_, ?_, ?_⟩
  · simp [PMF.map_comp, Function.comp_def]
  · simp [PMF.map_comp, Function.comp_def]
  · rw [PMF.toOuterMeasure_map_apply]
    have hsub : Prod.swap ⁻¹' {p : α × α | p.1 ≠ p.2} ⊆ {p : α × α | p.1 ≠ p.2} :=
      fun _ hp heq => hp heq.symm
    exact (measure_mono hsub).trans hω

/-- Monotonicity of `CoupledWithin` in the error bound `ε`. -/
theorem mono {μ ν : PMF α} {ε₁ ε₂ : ℝ≥0∞} (h : CoupledWithin μ ν ε₁) (hε : ε₁ ≤ ε₂) :
    CoupledWithin μ ν ε₂ := by
  obtain ⟨ω, h₁, h₂, hω⟩ := h
  exact ⟨ω, h₁, h₂, hω.trans hε⟩

/-- `CoupledWithin μ ν 0` holds if and only if `μ = ν`. -/
@[simp]
theorem zero_iff {μ ν : PMF α} : CoupledWithin μ ν 0 ↔ μ = ν := by
  constructor
  · rintro ⟨ω, rfl, rfl, hω⟩
    have hzero : ω.toOuterMeasure {p : α × α | p.1 ≠ p.2} = 0 := nonpos_iff_eq_zero.mp hω
    have hdisj : Disjoint ω.support {p : α × α | p.1 ≠ p.2} :=
      (PMF.toOuterMeasure_apply_eq_zero_iff ω _).mp hzero
    refine map_congr_on_support ω Prod.fst Prod.snd fun p hp => ?_
    by_contra hne
    exact Set.disjoint_left.mp hdisj hp hne
  · rintro rfl
    exact refl μ

/-- Deterministic postprocessing preserves `CoupledWithin` with the same error bound. -/
theorem map {μ ν : PMF α} {ε : ℝ≥0∞} (h : CoupledWithin μ ν ε) (f : α → β) :
    CoupledWithin (μ.map f) (ν.map f) ε := by
  obtain ⟨ω, rfl, rfl, hω⟩ := h
  refine ⟨ω.map (fun p => (f p.1, f p.2)), ?_, ?_, ?_⟩
  · simp [PMF.map_comp, Function.comp_def]
  · simp [PMF.map_comp, Function.comp_def]
  · rw [PMF.toOuterMeasure_map_apply]
    have hsub : (fun p : α × α => (f p.1, f p.2)) ⁻¹' {q : β × β | q.1 ≠ q.2} ⊆
        {p : α × α | p.1 ≠ p.2} :=
      fun p hp hfeq => hp (congrArg f hfeq)
    exact (measure_mono hsub).trans hω

/-- Composing two independent couplings via `g : α → β → γ` adds their disagreement bounds. -/
theorem map₂ {μ₁ ν₁ : PMF α} {μ₂ ν₂ : PMF β} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : CoupledWithin μ₁ ν₁ ε₁) (h₂ : CoupledWithin μ₂ ν₂ ε₂)
    (g : α → β → γ) :
    CoupledWithin
      (μ₁.bind fun a => μ₂.map (g a))
      (ν₁.bind fun a => ν₂.map (g a))
      (ε₁ + ε₂) := by
  obtain ⟨ω₁, rfl, rfl, hω₁⟩ := h₁
  obtain ⟨ω₂, rfl, rfl, hω₂⟩ := h₂
  refine ⟨ω₁.bind (fun p₁ => ω₂.map (fun p₂ => (g p₁.1 p₂.1, g p₁.2 p₂.2))), ?_, ?_, ?_⟩
  · rw [PMF.map_bind, PMF.bind_map]
    refine congrArg (ω₁.bind ·) (funext fun p₁ => ?_)
    simp [PMF.map_comp, Function.comp_def]
  · rw [PMF.map_bind, PMF.bind_map]
    refine congrArg (ω₁.bind ·) (funext fun p₁ => ?_)
    simp [PMF.map_comp, Function.comp_def]
  · let kern (p₁ : α × α) : PMF (γ × γ) :=
      ω₂.map (fun p₂ => (g p₁.1 p₂.1, g p₁.2 p₂.2))
    have hstep : ∀ p₁ ∈ ω₁.support, p₁ ∈ {p : α × α | p.1 = p.2} →
        (kern p₁).toOuterMeasure {q : γ × γ | q.1 ≠ q.2} ≤ ε₂ := by
      intro p₁ _ hp₁
      change p₁.1 = p₁.2 at hp₁
      dsimp only [kern]
      rw [PMF.toOuterMeasure_map_apply]
      have hsub :
          (fun p₂ : β × β => (g p₁.1 p₂.1, g p₁.2 p₂.2)) ⁻¹' {q : γ × γ | q.1 ≠ q.2} ⊆
            {p₂ : β × β | p₂.1 ≠ p₂.2} := by
        intro p₂ hp₂ hp₂_eq
        exact hp₂ (by change g p₁.1 p₂.1 = g p₁.2 p₂.2; rw [hp₁, hp₂_eq])
      exact (measure_mono hsub).trans hω₂
    have hfail := @toOuterMeasure_bind_failure_le (α × α) (γ × γ)
      ω₁ kern {p : α × α | p.1 = p.2} {q : γ × γ | q.1 ≠ q.2} ε₂ hstep
    have hcompl : ({p : α × α | p.1 = p.2}ᶜ : Set (α × α)) = {p : α × α | p.1 ≠ p.2} := by
      ext p
      simp
    rw [hcompl] at hfail
    exact hfail.trans (add_le_add hω₁ le_rfl)

/-- If a mixture `p.bind f` agrees with `q` on every `a ∈ p.support` belonging to a good event
`good : Set α`, then `p.bind f` is coupled with `q` within `p.toOuterMeasure goodᶜ`. -/
theorem bind_of_eq_on {p : PMF α} {f : α → PMF β} {q : PMF β} (good : Set α)
    (hgood : ∀ a ∈ p.support, a ∈ good → f a = q) :
    CoupledWithin (p.bind f) q (p.toOuterMeasure goodᶜ) := by
  classical
  let kernel (a : α) : PMF (β × β) :=
    if a ∈ good then
      (f a).map (fun b => (b, b))
    else
      (f a).bind (fun b₁ => q.map (fun b₂ => (b₁, b₂)))
  refine ⟨p.bind kernel, ?_, ?_, ?_⟩
  · rw [PMF.map_bind]
    refine congrArg (p.bind ·) (funext fun a => ?_)
    dsimp only [kernel]
    split_ifs
    · exact (PMF.map_comp _ _ _).trans (PMF.map_id _)
    · exact map_fst_bind_pair (f a) (fun _ => q)
  · rw [PMF.map_bind]
    have h2 : p.bind (fun a => (kernel a).map Prod.snd) = p.bind (fun _ => q) := by
      refine bind_congr_on_support p _ _ fun a ha => ?_
      dsimp only [kernel]
      split_ifs with h
      · rw [PMF.map_comp]
        exact (PMF.map_id _).trans (hgood a ha h)
      · rw [PMF.map_bind]
        have hq : (fun b₁ : β => (q.map (fun b₂ => (b₁, b₂))).map Prod.snd) = fun _ => q :=
          funext fun _ => (PMF.map_comp _ _ _).trans (PMF.map_id _)
        rw [hq, PMF.bind_const]
    rw [h2, PMF.bind_const]
  · have hstep : ∀ a ∈ p.support, a ∈ good →
        (kernel a).toOuterMeasure {pair : β × β | pair.1 ≠ pair.2} ≤ 0 := by
      intro a _ ha
      have hker : kernel a = (f a).map (fun b => (b, b)) := by simp [kernel, ha]
      rw [hker, nonpos_iff_eq_zero, PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      rintro ⟨b₁, b₂⟩ hmem hne
      obtain ⟨b, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
      exact hne ((congrArg Prod.fst heq).symm.trans (congrArg Prod.snd heq))
    simpa using toOuterMeasure_bind_failure_le p kernel good
      {pair : β × β | pair.1 ≠ pair.2} 0 hstep

/-- Coupling inequality for events: if `CoupledWithin μ ν ε`, then for every event `S : Set α`,
`μ.toOuterMeasure S ≤ ν.toOuterMeasure S + ε`. -/
theorem toOuterMeasure_le {μ ν : PMF α} {ε : ℝ≥0∞} (h : CoupledWithin μ ν ε) (S : Set α) :
    μ.toOuterMeasure S ≤ ν.toOuterMeasure S + ε := by
  obtain ⟨ω, rfl, rfl, hω⟩ := h
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  have hsub : Prod.fst ⁻¹' S ⊆ Prod.snd ⁻¹' S ∪ {p : α × α | p.1 ≠ p.2} := by
    intro p hp
    by_cases heq : p.1 = p.2
    · exact Or.inl (show p.2 ∈ S from heq ▸ hp)
    · exact Or.inr heq
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hω))

/-- On a finite type, `CoupledWithin μ ν ε` (with `ε ≠ ⊤`) bounds the statistical distance
`dist μ ν ≤ ε.toReal`. -/
theorem dist_le [Fintype α] {μ ν : PMF α} {ε : ℝ≥0∞} (h : CoupledWithin μ ν ε) (hε : ε ≠ ⊤) :
    dist μ ν ≤ ε.toReal := by
  obtain ⟨ω, rfl, rfl, hω⟩ := h
  exact (dist_map_map_le ω Prod.fst Prod.snd).trans (ENNReal.toReal_mono hε hω)

/-- On a finite measurable singleton space, `CoupledWithin μ ν ε` (with `ε ≠ ⊤`) bounds the
total variation distance `tvDist μ.toMeasure ν.toMeasure ≤ 2 * ε.toReal`. -/
theorem tvDist_le [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ ν : PMF α} {ε : ℝ≥0∞} (h : CoupledWithin μ ν ε) (hε : ε ≠ ⊤) :
    tvDist μ.toMeasure ν.toMeasure ≤ 2 * ε.toReal := by
  cases nonempty_fintype α
  have hdist := h.dist_le hε
  rw [dist_eq_tvDist_toMeasure_div_two] at hdist
  linarith

end CoupledWithin

end Cslib.Probability.PMF
