/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.Compression.Basic
public import CslibFrontier.MachineLearning.PACLearning.VCUniformConvergence
public import CslibFrontier.MachineLearning.PACLearning.VCUpperBound
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import CslibFrontier.MachineLearning.PACLearning.DualVCDimension
import CslibFrontier.MachineLearning.PACLearning.EpsilonApproximation
import CslibFrontier.Probability.Minimax
import CslibFrontier.Probability.PMF.Event

/-!
# Sample compression from finite VC dimension

Moran and Yehudayoff showed that every binary class of finite VC dimension `d` has a sample
compression scheme of size `exp(O(d))` [MoranYehudayoff2016, Theorem 1.3], which follows from
the size `O(d* d log (d* d))` bound in terms of the dual VC dimension `d*` [MoranYehudayoff2016,
Theorem 1.4] and Assouad's bound `d* < 2 ^ (d + 1)` (`DualVCDimension.lean`). This module
formalizes the construction in the proof of Theorem 1.4 [MoranYehudayoff2016, Claim 3.1], with
explicit sizes. Fix a consistent learner `A` for `C` that reads `s` examples, where `s` is the VC
sample size for accuracy `ε` and confidence `δ < 1`, and fix a sample `S` of `m` examples
realized by `C`.

* **Weak learning on subsamples.** For every distribution `q` on the positions of `S`, some
  sequence `b` of `s` positions has `A (S ∘ b)` wrong on a set of positions of `q`-probability at
  most `ε` (`IsConsistent.exists_subsample_toOuterMeasure_le`). This is the VC upper bound
  (`VCUpperBound.lean`) on the finite domain `Fin m` of positions, for the class `{c ∘ x | c ∈ C}`
  of traces of `C` on the sample points `x` and the pushforward of `q` along the labeling of `S`.
  A distribution on `Fin m` is automatically measurable, so no measurability hypothesis on `C` or
  `A` is needed.
* **Minimax.** Some distribution `μ` on such sequences has `A (S ∘ b)` wrong at every position of
  `S` with `μ`-probability at most `ε` (`IsConsistent.exists_pmf_subsample_toOuterMeasure_le`).
* **Sampling.** The votes `b ↦ A (S ∘ b) x` at the sample points form a pullback of the dual class
  of `C`, so their finite shattered sets have fewer than `2 ^ (d + 1)` points. An ε-approximation
  of `μ` for them (`EpsilonApproximation.lean`) gives `T` sequences `B t` such that at every
  example of `S` more than half of the hypotheses `A (S ∘ B t)` are right, for `ε = 1/4` and
  `T ≥ uniformConvergenceSampleSize (2 ^ (d + 1) - 1) (1/4) (1/2)`
  (`IsConsistent.exists_forall_lt_two_mul_card_filter`).
* **The scheme.** Compression keeps the `T` sequences of `s` indices, concatenated; positions may
  repeat. Reconstruction cuts the kept examples into `T` blocks of `s` and takes the majority vote
  of `A` on the blocks. No side information is needed, because a scheme here keeps an ordered list
  of indices (`SampleCompressionScheme.ofIsConsistent`, `SampleCompressionScheme.ofVCDim`).

With `ε = 1/4` in both steps and `δ = 1/2`, the size is
`vcCompressionSize d = ⌈uniformConvergenceSampleSize (2 ^ (d + 1) - 1) (1/4) (1/2)⌉ *
⌈vcSampleSize d (1/4) (1/2)⌉`, which is `O(2 ^ d) * O(d) = 2 ^ O(d)`. The source uses
`ε = 1/3` and `1/8` and the sharper `O(d* / ε²)` approximation size, giving `O(d* d)` kept
examples; the approximation size here, `O(d* log (1 / ε) / ε²)`, is also `O(d*)` at fixed `ε`.
The compression maps are semantic; no running time is claimed.

## Main definitions

- `vcCompressionBlockSize d`, `vcCompressionBlockCount d`, `vcCompressionSize d`: the explicit
  subsample size, number of subsamples and scheme size.
- `SampleCompressionScheme.ofIsConsistent`: the scheme built from a consistent learner.
- `SampleCompressionScheme.ofVCDim`: a scheme of size `vcCompressionSize d` for every class whose
  finite shattered sets have at most `d` points.

## Main results

- `IsConsistent.exists_subsample_toOuterMeasure_le`: weak learning on subsamples.
- `IsConsistent.exists_pmf_subsample_toOuterMeasure_le`: a distribution on subsamples that is
  right with probability at least `1 - ε` at every example.
- `IsConsistent.exists_forall_lt_two_mul_card_filter`: `T` subsamples whose majority is right at
  every example.
- `SampleCompressionScheme.exists_of_hasFiniteVCDim`: every binary class of finite VC dimension
  has a sample compression scheme of finite size.

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

/-- The uniform convergence sample size at `ε = 1/4`, `δ = 1/2` is positive. -/
private theorem uniformConvergenceSampleSize_quarter_half_pos (d : ℕ) :
    0 < uniformConvergenceSampleSize d (1 / 4) (1 / 2) := by
  unfold uniformConvergenceSampleSize
  have h1 : 0 < Real.log (4 / (1 / 2) : ℝ) := Real.log_pos (by norm_num)
  have h2 : 0 ≤ Real.log (10 / (1 / 4) : ℝ) := Real.log_nonneg (by norm_num)
  positivity

/-- **A majority of a few subsamples is right everywhere** [MoranYehudayoff2016, Claim 3.1]. Let
`A` be a consistent learner for `C` reading `s ≥ vcSampleSize d (1/4) (1/2)` examples, where every
finite set shattered by `C` has at most `d` points, and let
`T ≥ uniformConvergenceSampleSize (2 ^ (d + 1) - 1) (1/4) (1/2)`. For every nonempty sample `S`
realized by `C` there are `T` sequences `B t` of `s` positions such that at each example of `S`
more than half of the hypotheses `A (S ∘ B t)` are right. -/
theorem IsConsistent.exists_forall_lt_two_mul_card_filter {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {s : ℕ} {A : Learner α Bool s}
    (hA : IsConsistent A C) (hs : vcSampleSize d (1 / 4) (1 / 2) ≤ s) {T : ℕ}
    (hT : uniformConvergenceSampleSize (2 ^ (d + 1) - 1) (1 / 4) (1 / 2) ≤ T) {m : ℕ}
    (hm : 0 < m) {S : LabeledSample α Bool m} (hS : Realizable C S) :
    ∃ B : Fin T → Fin s → Fin m, ∀ i,
      T < 2 * (Finset.univ.filter fun t => A (S ∘ B t) (S i).1 = (S i).2).card := by
  classical
  obtain ⟨μ, hμ⟩ := hA.exists_pmf_subsample_toOuterMeasure_le hC (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hs hm hS
  -- Every subsample of `S` is realizable, so `A` returns a concept of `C` on it.
  have hsub (b : Fin s → Fin m) : A (S ∘ b) ∈ C := by
    obtain ⟨c, hc, hcS⟩ := hS
    exact hA.output_mem_conceptClass _ ⟨c, hc, fun j => hcS (b j)⟩
  let φ : (Fin s → Fin m) → ↥C := fun b => ⟨A (S ∘ b), hsub b⟩
  -- The votes at the examples of `S`, as a class on subsamples: a pullback of the dual class.
  let G : ConceptClass (Fin s → Fin m) Bool := range fun i b => A (S ∘ b) (S i).1
  have hGsub : G ⊆ (fun g => g ∘ φ) '' dualClass C := by
    rintro _ ⟨i, rfl⟩
    exact ⟨_, mem_dualClass.2 ⟨(S i).1, rfl⟩, rfl⟩
  have hG : ∀ W : Finset (Fin s → Fin m), SetShatters G ↑W → W.card ≤ 2 ^ (d + 1) - 1 :=
    fun _ hW => (hW.superset hGsub).card_le_of_comp
      (fun _ hF => card_le_of_setShatters_dualClass hC hF)
  -- An ε-approximation of `μ` for the votes, with `ε = 1/4`.
  obtain ⟨B, hB⟩ := exists_isEpsApprox_of_uniformConvergenceSampleSize_le μ.toMeasure hG
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hT
  have hTpos : (0 : ℝ) < T :=
    (uniformConvergenceSampleSize_quarter_half_pos _).trans_le hT
  refine ⟨B, fun i => ?_⟩
  have hBi := hB _ ⟨i, rfl⟩
  simp only at hBi
  rw [μ.toMeasure_apply_eq_toOuterMeasure] at hBi
  have hwrong := hμ i
  have hwrong' : (μ.toOuterMeasure {b | A (S ∘ b) (S i).1 ≠ (S i).2}).toReal ≤ 1 / 4 :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num) hwrong
  have hsum := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl μ
    {b | A (S ∘ b) (S i).1 = true}
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin T)))
    (fun t => A (S ∘ B t) (S i).1 = true)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hTc : (T : ℝ) = (Finset.univ.filter fun t => A (S ∘ B t) (S i).1 = true).card +
      (Finset.univ.filter fun t => ¬ A (S ∘ B t) (S i).1 = true).card := by
    exact_mod_cast hcard.symm
  rw [abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add, div_lt_iff₀ hTpos, lt_div_iff₀ hTpos] at hBi
  rcases hy : (S i).2 with _ | _
  · -- label `false`: the wrong votes are the `true` votes, of probability at most `1/4`
    have hset : {b | A (S ∘ b) (S i).1 ≠ (S i).2} = {b | A (S ∘ b) (S i).1 = true} := by
      ext b; simp [hy]
    rw [hset] at hwrong'
    have hfilt : (Finset.univ.filter fun t => A (S ∘ B t) (S i).1 = false) =
        Finset.univ.filter fun t => ¬ A (S ∘ B t) (S i).1 = true := by
      simp only [Bool.not_eq_true]
    rw [hfilt]
    have : (T : ℝ) < 2 * (Finset.univ.filter fun t => ¬ A (S ∘ B t) (S i).1 = true).card := by
      nlinarith [hBi.2]
    exact_mod_cast this
  · -- label `true`: the wrong votes are the `false` votes, of probability at most `1/4`
    have hset : {b | A (S ∘ b) (S i).1 ≠ (S i).2} = {b | A (S ∘ b) (S i).1 = true}ᶜ := by
      ext b; simp [hy]
    rw [hset] at hwrong'
    have : (T : ℝ) < 2 * (Finset.univ.filter fun t => A (S ∘ B t) (S i).1 = true).card := by
      nlinarith [hBi.1]
    exact_mod_cast this


/-- The Moran–Yehudayoff subsample size for VC dimension `d`: `⌈vcSampleSize d (1/4) (1/2)⌉`. -/
@[expose] noncomputable def vcCompressionBlockSize (d : ℕ) : ℕ :=
  ⌈vcSampleSize d (1 / 4) (1 / 2)⌉₊

/-- The Moran–Yehudayoff number of subsamples for VC dimension `d`:
`⌈uniformConvergenceSampleSize (2 ^ (d + 1) - 1) (1/4) (1/2)⌉`. -/
@[expose] noncomputable def vcCompressionBlockCount (d : ℕ) : ℕ :=
  ⌈uniformConvergenceSampleSize (2 ^ (d + 1) - 1) (1 / 4) (1 / 2)⌉₊

/-- The size of the Moran–Yehudayoff compression scheme for VC dimension `d`:
`vcCompressionBlockCount d * vcCompressionBlockSize d`. -/
@[expose] noncomputable def vcCompressionSize (d : ℕ) : ℕ :=
  vcCompressionBlockCount d * vcCompressionBlockSize d

/-- Majority vote over `T` blocks of `s` examples of a list: block `t` is the entries
`s t + j`, `j < s` (padded beyond the end of the list), and the vote at `x` is `true` iff more than
half of the hypotheses `A` on the blocks say `true` at `x`. -/
private def blockMajority {s : ℕ} (A : Learner α Bool s) (T : ℕ) (l : List (α × Bool)) (x : α) :
    Bool :=
  decide (T < 2 * (Finset.univ.filter fun t : Fin T =>
    A (fun j => l.getD (j + s * t) (x, false)) x = true).card)

open Classical in
/-- The kept indices: `T` sequences of `s` positions whose hypotheses are right by majority at
every example of `S`, concatenated, when they exist. -/
private noncomputable def majorityIndices {s : ℕ} (A : Learner α Bool s) (T : ℕ) {m : ℕ}
    (S : LabeledSample α Bool m) : List (Fin m) :=
  if h : ∃ B : Fin T → Fin s → Fin m, ∀ i,
      T < 2 * (Finset.univ.filter fun t => A (S ∘ B t) (S i).1 = (S i).2).card then
    List.ofFn fun k : Fin (T * s) => h.choose (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  else []

namespace SampleCompressionScheme

/-- The Moran–Yehudayoff compression scheme built from a consistent learner `A` reading
`s ≥ vcSampleSize d (1/4) (1/2)` examples, with `T ≥ uniformConvergenceSampleSize
(2 ^ (d + 1) - 1) (1/4) (1/2)` subsamples. It keeps `T` subsamples of `s` examples each,
concatenated, and reconstructs by the majority vote of `A` on them. -/
noncomputable def ofIsConsistent {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {s : ℕ} {A : Learner α Bool s}
    (hA : IsConsistent A C) (hs : vcSampleSize d (1 / 4) (1 / 2) ≤ s) {T : ℕ}
    (hT : uniformConvergenceSampleSize (2 ^ (d + 1) - 1) (1 / 4) (1 / 2) ≤ T) :
    SampleCompressionScheme C (T * s) where
  compress S := majorityIndices A T S
  reconstruct := blockMajority A T
  length_compress_le S _ := by
    unfold majorityIndices
    split <;> simp
  reconstruct_correct S hS i := by
    classical
    have hB := hA.exists_forall_lt_two_mul_card_filter hC hs hT (Fin.pos i) hS
    unfold majorityIndices
    rw [dite_eq_left_of_eq_true (eq_true hB)]
    set B := hB.choose
    have hblock (t : Fin T) : (fun j : Fin s => ((List.ofFn fun k : Fin (T * s) =>
        B (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).map S).getD (j + s * t)
          ((S i).1, false)) = S ∘ B t := by
      funext j
      have hk : (j : ℕ) + s * t < T * s := (finProdFinEquiv (t, j)).2
      rw [List.map_ofFn, ← List.getElem_eq_getD ((S i).1, false) (h := by simpa using hk),
        List.getElem_ofFn]
      have : finProdFinEquiv.symm (⟨j + s * t, hk⟩ : Fin (T * s)) = (t, j) :=
        finProdFinEquiv.symm_apply_eq.2 (Fin.ext (by simp))
      simp only [Function.comp_apply, this]
    have hmaj : T < 2 * (Finset.univ.filter fun t => A (S ∘ B t) (S i).1 = (S i).2).card :=
      hB.choose_spec i
    unfold blockMajority
    simp only [hblock]
    have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin T)))
      (fun t => A (S ∘ B t) (S i).1 = true)
    simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at hcard
    rcases hy : (S i).2 with _ | _ <;> rw [hy] at hmaj
    · simp only [decide_eq_false_iff_not, not_lt]
      omega
    · simpa using hmaj

/-- Some learner reading `m` examples is consistent with `C`: a consistent one when `C` is
nonempty, and any learner when `C` is empty, since then no sample is realizable. -/
private theorem exists_isConsistent_learner (C : ConceptClass α Bool) (m : ℕ) :
    ∃ A : Learner α Bool m, IsConsistent A C := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => false, fun _ ⟨_, hc, _⟩ => absurd hc (Set.notMem_empty _)⟩
  · exact exists_isConsistent hne

/-- **Sample compression from finite VC dimension** [MoranYehudayoff2016, Theorems 1.3 and 1.4]:
a binary class whose finite shattered sets have at most `d` points has a sample compression scheme
of size `vcCompressionSize d`, which is `2 ^ O(d)`. -/
noncomputable def ofVCDim {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) :
    SampleCompressionScheme C (vcCompressionSize d) :=
  ofIsConsistent hC (exists_isConsistent_learner C (vcCompressionBlockSize d)).choose_spec
    (Nat.le_ceil _) (Nat.le_ceil _)

/-- Every binary class of finite VC dimension has a sample compression scheme of finite size
[MoranYehudayoff2016, Theorem 1.3]. -/
theorem exists_of_hasFiniteVCDim {C : ConceptClass α Bool} (hC : HasFiniteVCDim C) :
    ∃ k, Nonempty (SampleCompressionScheme C k) :=
  ⟨_, ⟨ofVCDim fun _ hW => hW.card_le_vcDim hC⟩⟩

end SampleCompressionScheme

end Cslib.MachineLearning.PACLearning
