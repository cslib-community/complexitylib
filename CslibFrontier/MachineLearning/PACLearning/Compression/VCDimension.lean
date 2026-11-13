/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.VCUpperBound
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import CslibFrontier.MachineLearning.PACLearning.DualVCDimension
import CslibFrontier.Probability.Minimax
import CslibFrontier.Probability.PMF.Event

/-!
# Sample compression from finite VC dimension: voting over subsamples

Moran and Yehudayoff showed that every binary class of finite VC dimension `d` has a sample
compression scheme of size `exp(O(d))` [MoranYehudayoff2016, Theorem 1.3], which follows from
the size `O(d* d log (d* d))` bound in terms of the dual VC dimension `d*` [MoranYehudayoff2016,
Theorem 1.4] and Assouad's bound `d* < 2 ^ (d + 1)` (`DualVCDimension.lean`). The proof of
Theorem 1.4 starts from a *weak learner on subsamples* [MoranYehudayoff2016, proof of
Claim 3.1]. Fix a consistent learner `A` for `C` that reads `s` examples, where `s` is the VC
sample size for accuracy `ε` and confidence `δ < 1`, and fix a sample `S` of `m` examples realized
by `C`. Then:

* for every distribution `q` on the positions of `S`, some sequence `b` of `s` positions has
  `A (S ∘ b)` wrong on a set of positions of `q`-probability at most `ε`
  (`IsConsistent.exists_subsample_toOuterMeasure_le`);
* by the minimax theorem, some distribution `μ` on such sequences has `A (S ∘ b)` wrong at every
  position of `S` with `μ`-probability at most `ε`
  (`IsConsistent.exists_pmf_subsample_toOuterMeasure_le`).

The first statement is the VC upper bound (`VCUpperBound.lean`) applied on the finite domain
`Fin m` of positions, to the class `{c ∘ x | c ∈ C}` of traces of `C` on the sample points `x` and
to the pushforward of `q` along the labeling of `S`. A distribution on `Fin m` is automatically
measurable, so no measurability hypothesis on `C` or `A` is needed. Positions may repeat in `b`.

## Main results

- `IsConsistent.exists_subsample_toOuterMeasure_le`: weak learning on subsamples.
- `IsConsistent.exists_pmf_subsample_toOuterMeasure_le`: a distribution on subsamples that is
  right with probability at least `1 - ε` at every example.

## References

* [S. Moran, A. Yehudayoff, *Sample compression schemes for VC classes*][MoranYehudayoff2016]
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*}

/-- **Weak learning on subsamples** [MoranYehudayoff2016, proof of Claim 3.1]. Let `A` be a
consistent learner for `C` reading `s ≥ vcSampleSize d ε δ` examples with `δ < 1`, where every
finite set shattered by `C` has at most `d` points. For every sample `S` realized by `C` and every
distribution `q` on its positions, some sequence `b` of `s` positions has `A (S ∘ b)` wrong on a
set of positions of `q`-probability at most `ε`. -/
theorem IsConsistent.exists_subsample_toOuterMeasure_le {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {s : ℕ} {A : Learner α Bool s}
    (hA : IsConsistent A C) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hs : vcSampleSize d ε δ ≤ s) {m : ℕ} {S : LabeledSample α Bool m} (hS : Realizable C S)
    (q : PMF (Fin m)) :
    ∃ b : Fin s → Fin m,
      q.toOuterMeasure {i | A (S ∘ b) (S i).1 ≠ (S i).2} ≤ ENNReal.ofReal ε := by
  obtain ⟨c₀, hc₀, hc₀S⟩ := hS
  -- Learn the traces of `C` on the sample points, over the positions of the sample.
  let x : Fin m → α := fun i => (S i).1
  let y : Fin m → Bool := fun i => (S i).2
  let C' : ConceptClass (Fin m) Bool := (fun c => c ∘ x) '' C
  have hC' : ∀ W : Finset (Fin m), SetShatters C' ↑W → W.card ≤ d :=
    fun _ hW => hW.card_le_of_comp hC
  let A' : Learner (Fin m) Bool s := fun T => A (fun j => (x (T j).1, (T j).2)) ∘ x
  have hA' : IsConsistent A' C' := by
    rintro T ⟨_, ⟨c, hc, rfl⟩, hcT⟩
    obtain ⟨hAC, hAT⟩ := hA (fun j => (x (T j).1, (T j).2)) ⟨c, hc, hcT⟩
    exact ⟨⟨_, hAC, rfl⟩, hAT⟩
  let D : Measure (Fin m × Bool) := (q.map fun i => (i, y i)).toMeasure
  have hD_apply (t : Set (Fin m × Bool)) : D t = q.toOuterMeasure ((fun i => (i, y i)) ⁻¹' t) := by
    rw [PMF.toMeasure_apply_eq_toOuterMeasure, PMF.toOuterMeasure_map_apply]
  have hD : IsRealizableBy D C' := by
    refine ⟨c₀ ∘ x, ⟨c₀, hc₀, rfl⟩, ?_⟩
    have : (fun i => (i, y i)) ⁻¹' {p : Fin m × Bool | (c₀ ∘ x) p.1 ≠ p.2} = ∅ := by
      ext i
      simp [x, y, hc₀S i]
    rw [error, hD_apply, this, measure_empty]
  have hbad := hA'.measure_pi_lt_error_le_of_vcSampleSize_le hC' hD hε hε1 hδ hδ1.le hs
  -- Almost every sample of positions carries the labels of `S`, so `A'` runs `A` on a subsample.
  have hgraph : ∀ᵐ p ∂D, p.2 = y p.1 := by
    have : (fun i => (i, y i)) ⁻¹' {p : Fin m × Bool | ¬ p.2 = y p.1} = ∅ := by
      ext i
      simp
    rw [ae_iff, hD_apply, this, measure_empty]
  have hon : ∀ᵐ T ∂Measure.pi (fun _ : Fin s => D), ∀ j, (T j).2 = y (T j).1 :=
    ae_all_iff.2 fun j => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin s => D) (i := j)).eventually
      hgraph
  by_contra hne
  simp only [not_exists, not_le] at hne
  have hall : ∀ᵐ T ∂Measure.pi (fun _ : Fin s => D), ENNReal.ofReal ε < error D (A' T) := by
    filter_upwards [hon] with T hT
    have hAT : A' T = A (S ∘ fun j => (T j).1) ∘ x := by
      have : (fun j => (x (T j).1, (T j).2)) = S ∘ fun j => (T j).1 :=
        funext fun j => Prod.ext rfl (hT j)
      simp only [A', this]
    rw [error, hD_apply, hAT]
    exact hne _
  have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ :=
    calc (1 : ℝ≥0∞) = Measure.pi (fun _ : Fin s => D) univ := measure_univ.symm
      _ ≤ Measure.pi (fun _ : Fin s => D) {T | ENNReal.ofReal ε < error D (A' T)} :=
        measure_mono_ae (hall.mono fun _ h _ => h)
      _ ≤ ENNReal.ofReal δ := hbad
  exact absurd hle (not_le.2 (ENNReal.ofReal_lt_one.2 hδ1))

/-- **A distribution on subsamples that is right everywhere** [MoranYehudayoff2016, proof of
Claim 3.1, via Theorem 2.3]. Under the hypotheses of
`IsConsistent.exists_subsample_toOuterMeasure_le`, for every nonempty sample `S` realized by `C`,
some distribution `μ` on sequences `b` of `s` positions has `A (S ∘ b)` wrong at each example of
`S` with `μ`-probability at most `ε`. This is the minimax
theorem `Cslib.Probability.PMF.exists_forall_toOuterMeasure_le` applied to weak learning on
subsamples. -/
theorem IsConsistent.exists_pmf_subsample_toOuterMeasure_le {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {s : ℕ} {A : Learner α Bool s}
    (hA : IsConsistent A C) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hs : vcSampleSize d ε δ ≤ s) {m : ℕ} (hm : 0 < m) {S : LabeledSample α Bool m}
    (hS : Realizable C S) :
    ∃ μ : PMF (Fin s → Fin m),
      ∀ i, μ.toOuterMeasure {b | A (S ∘ b) (S i).1 ≠ (S i).2} ≤ ENNReal.ofReal ε := by
  have : Nonempty (Fin s → Fin m) := ⟨fun _ => ⟨0, hm⟩⟩
  obtain ⟨μ, -, hμ⟩ := Cslib.Probability.PMF.exists_forall_toOuterMeasure_le
    (fun b i => A (S ∘ b) (S i).1 ≠ (S i).2) fun q => by
      obtain ⟨b, hb⟩ := hA.exists_subsample_toOuterMeasure_le hC hε hε1 hδ hδ1 hs hS q
      exact ⟨b, ENNReal.toReal_le_of_le_ofReal hε.le hb⟩
  exact ⟨μ, fun i => (ENNReal.le_ofReal_iff_toReal_le
    (Cslib.Probability.PMF.toOuterMeasure_ne_top μ _) hε.le).2 (hμ i)⟩

end Cslib.MachineLearning.PACLearning
