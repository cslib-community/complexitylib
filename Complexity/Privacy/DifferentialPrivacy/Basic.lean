/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF.Event
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Differential privacy

A mechanism is a map `M : D → PMF R` from datasets to output distributions. It is
`(ε, δ)`-differentially private with respect to an adjacency relation `Adj` on datasets when
`Pr[M x ∈ S] ≤ exp ε · Pr[M y ∈ S] + δ` for every pair of adjacent datasets `x`, `y` and every
event `S ⊆ R` [DworkRoth2014, Definition 2.4]. Events are arbitrary sets of outputs, measured by
`PMF.toOuterMeasure`, so no measurable structure on `R` is needed.

The adjacency relation is a parameter. Dwork and Roth compare databases at `ℓ₁` distance at most
one (adding or removing one record); Ghosh, Roughgarden and Sundararajan compare databases that
coincide in all but one row [GhoshRoughgardenSundararajan2012, §2.1], which is
`Cslib.Privacy.HammingAdjacent` in `Complexity.Privacy.DifferentialPrivacy.Hamming`. Both are
instances. The definition quantifies over ordered pairs, so a symmetric guarantee needs a symmetric
`Adj`.

The pointwise characterization of pure privacy (`DifferentiallyPrivate.iff_apply_le`) is the
likelihood-ratio form used for mechanisms with a countable range
[GhoshRoughgardenSundararajan2012, §2.1]. It follows from the hockey-stick characterization
(`DifferentiallyPrivate.iff_tsum_tsub_le`): the optimal `δ` for a fixed factor `exp ε` is the
total excess `∑ r, (M x r - exp ε · M y r)`.

## Main definitions

* `Cslib.Privacy.DifferentiallyPrivate`: `(ε, δ)`-differential privacy relative to `Adj`.

## Main results

* `Cslib.Privacy.DifferentiallyPrivate.iff_tsum_tsub_le`: the hockey-stick characterization.
* `Cslib.Privacy.DifferentiallyPrivate.iff_apply_le`: pure privacy is a pointwise ratio bound.
* `Cslib.Privacy.DifferentiallyPrivate.bind`, `Cslib.Privacy.DifferentiallyPrivate.map`:
  post-processing by an arbitrary randomized or deterministic map [DworkRoth2014, Prop. 2.1].
* `Cslib.Privacy.DifferentiallyPrivate.trans`: privacy along a composite of two adjacency
  relations, the inductive step of group privacy.

## References

* [DworkRoth2014]
* [GhoshRoughgardenSundararajan2012]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

universe u v w

variable {D : Type u} {R : Type v} {R' : Type w}

/-- A mechanism `M` is `(ε, δ)`-differentially private with respect to the adjacency relation
`Adj` when, for all adjacent datasets `x`, `y` and every event `S`,
`Pr[M x ∈ S] ≤ exp ε · Pr[M y ∈ S] + δ` [DworkRoth2014, Definition 2.4]. -/
@[expose] def DifferentiallyPrivate (Adj : D → D → Prop) (M : D → PMF R) (ε : ℝ) (δ : ℝ≥0∞) :
    Prop :=
  ∀ ⦃x y⦄, Adj x y → ∀ S : Set R,
    (M x).toOuterMeasure S ≤ ENNReal.ofReal (Real.exp ε) * (M y).toOuterMeasure S + δ

section HockeyStick

variable {α : Type*}

/-- For a finite factor `c`, the event bounds `Pr_p[S] ≤ c · Pr_q[S] + δ` hold for all events
exactly when the total excess `∑ a, (p a - c · q a)` (the hockey-stick divergence) is at most
`δ`. The event attaining the excess is `{a | c · q a < p a}`. -/
theorem toOuterMeasure_le_mul_add_iff_tsum_tsub_le (p q : PMF α) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (δ : ℝ≥0∞) :
    (∀ S : Set α, p.toOuterMeasure S ≤ c * q.toOuterMeasure S + δ) ↔
      ∑' a, (p a - c * q a) ≤ δ := by
  classical
  constructor
  · intro h
    set T : Set α := {a | c * q a < p a}
    have hsplit : p.toOuterMeasure T = c * q.toOuterMeasure T + ∑' a, (p a - c * q a) := by
      rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left,
        ← tsum_add]
      refine tsum_congr fun a => ?_
      by_cases ha : a ∈ T
      · simp only [Set.indicator_of_mem ha]
        exact (add_tsub_cancel_of_le (le_of_lt ha)).symm
      · have hle : p a ≤ c * q a := not_lt.mp ha
        simp only [Set.indicator_of_notMem ha, mul_zero, zero_add, tsub_eq_zero_of_le hle]
    have hfin : c * q.toOuterMeasure T ≠ ⊤ :=
      ENNReal.mul_ne_top hc (Probability.PMF.toOuterMeasure_ne_top q T)
    have := h T
    rw [hsplit] at this
    exact (ENNReal.add_le_add_iff_left hfin).mp this
  · intro h S
    calc p.toOuterMeasure S = ∑' a, S.indicator p a := PMF.toOuterMeasure_apply p S
      _ ≤ ∑' a, (c * S.indicator q a + (p a - c * q a)) := by
        refine tsum_le_tsum fun a => ?_
        by_cases ha : a ∈ S
        · simp only [Set.indicator_of_mem ha]
          exact le_add_tsub
        · simp only [Set.indicator_of_notMem ha, mul_zero, zero_add]
          exact zero_le
      _ = c * q.toOuterMeasure S + ∑' a, (p a - c * q a) := by
        rw [tsum_add, ENNReal.tsum_mul_left, PMF.toOuterMeasure_apply]
      _ ≤ c * q.toOuterMeasure S + δ := by gcongr

/-- Expectations of a `[0, 1]`-valued function under `p` and `q` differ by at most the
hockey-stick divergence: `E_p[g] ≤ c · E_q[g] + ∑ a, (p a - c · q a)`. -/
theorem tsum_mul_le_mul_tsum_mul_add (p q : PMF α) (c : ℝ≥0∞) {g : α → ℝ≥0∞}
    (hg : ∀ a, g a ≤ 1) :
    ∑' a, p a * g a ≤ c * ∑' a, q a * g a + ∑' a, (p a - c * q a) := by
  calc ∑' a, p a * g a ≤ ∑' a, (c * (q a * g a) + (p a - c * q a)) := by
        refine tsum_le_tsum fun a => ?_
        calc p a * g a ≤ (c * q a + (p a - c * q a)) * g a := by gcongr; exact le_add_tsub
          _ = c * (q a * g a) + (p a - c * q a) * g a := by ring
          _ ≤ c * (q a * g a) + (p a - c * q a) := by
            gcongr
            calc (p a - c * q a) * g a ≤ (p a - c * q a) * 1 := by gcongr; exact hg a
              _ = p a - c * q a := mul_one _
    _ = c * ∑' a, q a * g a + ∑' a, (p a - c * q a) := by
        rw [tsum_add, ENNReal.tsum_mul_left]

end HockeyStick

namespace DifferentiallyPrivate

variable {Adj : D → D → Prop} {M : D → PMF R} {ε : ℝ} {δ : ℝ≥0∞}

/-- `(ε, δ)`-differential privacy bounds the hockey-stick divergence of adjacent output
distributions at factor `exp ε` by `δ`, and conversely. -/
theorem iff_tsum_tsub_le :
    DifferentiallyPrivate Adj M ε δ ↔
      ∀ ⦃x y⦄, Adj x y → ∑' r, (M x r - ENNReal.ofReal (Real.exp ε) * M y r) ≤ δ := by
  refine forall_congr' fun x => forall_congr' fun y => forall_congr' fun _ => ?_
  exact toOuterMeasure_le_mul_add_iff_tsum_tsub_le _ _ ENNReal.ofReal_ne_top δ

/-- Pure `(ε, 0)`-differential privacy is the pointwise likelihood-ratio bound
`M x r ≤ exp ε · M y r` [GhoshRoughgardenSundararajan2012, §2.1]. -/
theorem iff_apply_le :
    DifferentiallyPrivate Adj M ε 0 ↔
      ∀ ⦃x y⦄, Adj x y → ∀ r, M x r ≤ ENNReal.ofReal (Real.exp ε) * M y r := by
  rw [iff_tsum_tsub_le]
  refine forall_congr' fun x => forall_congr' fun y => forall_congr' fun _ => ?_
  rw [nonpos_iff_eq_zero, tsum_eq_zero_iff]
  exact forall_congr' fun r => tsub_eq_zero_iff_le

/-- A pointwise likelihood-ratio bound gives pure differential privacy. -/
theorem of_apply_le (h : ∀ ⦃x y⦄, Adj x y → ∀ r, M x r ≤ ENNReal.ofReal (Real.exp ε) * M y r) :
    DifferentiallyPrivate Adj M ε 0 :=
  iff_apply_le.mpr h

/-- Differential privacy bounds expectations of `[0, 1]`-valued functions:
`E[g (M x)] ≤ exp ε · E[g (M y)] + δ` for adjacent `x`, `y`. -/
theorem tsum_mul_le (h : DifferentiallyPrivate Adj M ε δ) {x y : D} (hxy : Adj x y)
    {g : R → ℝ≥0∞} (hg : ∀ r, g r ≤ 1) :
    ∑' r, M x r * g r ≤ ENNReal.ofReal (Real.exp ε) * ∑' r, M y r * g r + δ :=
  (tsum_mul_le_mul_tsum_mul_add _ _ _ hg).trans (by gcongr; exact iff_tsum_tsub_le.mp h hxy)

/-- Differential privacy is monotone in both privacy parameters. -/
theorem mono {ε' : ℝ} {δ' : ℝ≥0∞} (h : DifferentiallyPrivate Adj M ε δ) (hε : ε ≤ ε')
    (hδ : δ ≤ δ') : DifferentiallyPrivate Adj M ε' δ' := fun _ _ hxy S =>
  (h hxy S).trans (by gcongr)

/-- Differential privacy is antitone in the adjacency relation. -/
theorem mono_adj {Adj' : D → D → Prop} (h : DifferentiallyPrivate Adj M ε δ)
    (hAdj : ∀ ⦃x y⦄, Adj' x y → Adj x y) : DifferentiallyPrivate Adj' M ε δ :=
  fun _ _ hxy => h (hAdj hxy)

/-- Post-processing: applying any randomized map `K` to the output of a differentially private
mechanism preserves its privacy parameters [DworkRoth2014, Proposition 2.1]. -/
theorem bind (h : DifferentiallyPrivate Adj M ε δ) (K : R → PMF R') :
    DifferentiallyPrivate Adj (fun x => (M x).bind K) ε δ := by
  intro x y hxy S
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  exact h.tsum_mul_le hxy fun r => Probability.PMF.toOuterMeasure_le_one _ _

/-- Deterministic post-processing preserves differential privacy. -/
theorem map (h : DifferentiallyPrivate Adj M ε δ) (f : R → R') :
    DifferentiallyPrivate Adj (fun x => (M x).map f) ε δ := by
  intro x y hxy S
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact h hxy _

/-- Precomposing a mechanism with a map that sends `Adj'`-adjacent datasets to `Adj`-adjacent
ones preserves differential privacy. -/
theorem comp {D' : Type*} {Adj' : D' → D' → Prop} (h : DifferentiallyPrivate Adj M ε δ)
    (f : D' → D) (hf : ∀ ⦃x y⦄, Adj' x y → Adj (f x) (f y)) :
    DifferentiallyPrivate Adj' (M ∘ f) ε δ := fun _ _ hxy => h (hf hxy)

/-- Privacy along the composite of two adjacency relations: if `M` is `(ε₁, δ₁)`-private for
`Adj₁` and `(ε₂, δ₂)`-private for `Adj₂`, it is `(ε₁ + ε₂, δ₁ + exp ε₁ · δ₂)`-private for
`Relation.Comp Adj₁ Adj₂`. -/
theorem trans {Adj₁ Adj₂ : D → D → Prop} {ε₁ ε₂ : ℝ} {δ₁ δ₂ : ℝ≥0∞}
    (h₁ : DifferentiallyPrivate Adj₁ M ε₁ δ₁) (h₂ : DifferentiallyPrivate Adj₂ M ε₂ δ₂) :
    DifferentiallyPrivate (Relation.Comp Adj₁ Adj₂) M (ε₁ + ε₂)
      (δ₁ + ENNReal.ofReal (Real.exp ε₁) * δ₂) := by
  rintro x z ⟨y, hxy, hyz⟩ S
  calc (M x).toOuterMeasure S
      ≤ ENNReal.ofReal (Real.exp ε₁) * (M y).toOuterMeasure S + δ₁ := h₁ hxy S
    _ ≤ ENNReal.ofReal (Real.exp ε₁) *
          (ENNReal.ofReal (Real.exp ε₂) * (M z).toOuterMeasure S + δ₂) + δ₁ := by
        gcongr; exact h₂ hyz S
    _ = ENNReal.ofReal (Real.exp (ε₁ + ε₂)) * (M z).toOuterMeasure S +
          (δ₁ + ENNReal.ofReal (Real.exp ε₁) * δ₂) := by
        rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring

end DifferentiallyPrivate

end Cslib.Privacy
