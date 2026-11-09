/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MinEntropy
import CslibFrontier.Probability.StatisticalDistance

/-!
# Seeded randomness extractors

A *`(k, ε)`-extractor* `ext : Input → Seed → Output` turns every source of min-entropy at least `k`,
together with an independent uniform seed, into an output within statistical distance `ε` of
uniform (`Cslib.Probability.IsExtractor`). It is *strong* if the output stays `ε`-close to uniform
even when the seed is revealed: the pair `(seed, ext x seed)` is `ε`-close to a uniform pair
(`Cslib.Probability.IsStrongExtractor`) [Nisan, Zuckerman][NisanZuckerman1996],
[Vadhan, Chapter 6][Vadhan2012].

Strong extractors are extractors (`IsStrongExtractor.isExtractor`), and both notions apply to
`(k, δ)`-sources at the cost of `δ` (`IsExtractor.dist_le_of_isSource`,
`IsStrongExtractor.dist_le_of_isSource`).

The seed cannot be dropped. Without one, no function to `Bool` extracts even from sources missing
only one bit of min-entropy: some output value has at least half of the inputs as preimages, and
the uniform distribution on those inputs makes the output constant
(`not_isExtractor_bool_of_subsingleton`) [Vadhan, Chapter 6][Vadhan2012]. Seeded extractors and
two-source extractors are the two standard ways around this.

## Main definitions

* `Cslib.Probability.IsExtractor`: `(k, ε)`-extractors.
* `Cslib.Probability.IsStrongExtractor`: strong `(k, ε)`-extractors, whose seed may be revealed.

## Main results

* `Cslib.Probability.IsStrongExtractor.isExtractor`: strong extractors are extractors.
* `Cslib.Probability.IsExtractor.dist_le_of_isSource`,
  `Cslib.Probability.IsStrongExtractor.dist_le_of_isSource`: extraction from `(k, δ)`-sources.
* `Cslib.Probability.not_isExtractor_bool_of_subsingleton`: seedless extraction of one bit fails
  for sources missing one bit of min-entropy.

## References

* [N. Nisan, D. Zuckerman, *Randomness is Linear in Space*][NisanZuckerman1996]
* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Chapter 6
-/

@[expose] public section

namespace Cslib.Probability

open Cslib.Probability.PMF
open scoped NNReal

variable {Input Seed Output : Type*} [Fintype Seed] [Nonempty Seed] [Fintype Output]
  [Nonempty Output]

/-- A **`(k, ε)`-extractor**: for every source of min-entropy at least `k`, applying `ext` to a
sample of the source and an independent uniform seed gives an output within statistical distance
`ε` of uniform. -/
def IsExtractor (ext : Input → Seed → Output) (k ε : ℝ) : Prop :=
  ∀ source : PMF Input, k ≤ minEntropy source →
    dist (source.bind fun x => (PMF.uniformOfFintype Seed).map fun s => ext x s)
      (PMF.uniformOfFintype Output) ≤ ε

/-- A **strong `(k, ε)`-extractor**: for every source of min-entropy at least `k`, the seed paired
with the output of `ext` is within statistical distance `ε` of a uniform pair, so the output stays
nearly uniform even given the seed. -/
def IsStrongExtractor (ext : Input → Seed → Output) (k ε : ℝ) : Prop :=
  ∀ source : PMF Input, k ≤ minEntropy source →
    dist (source.bind fun x => (PMF.uniformOfFintype Seed).map fun s => (s, ext x s))
      (PMF.uniformOfFintype (Seed × Output)) ≤ ε

variable {ext : Input → Seed → Output} {k k' ε ε' : ℝ}

/-- Extractors remain extractors for sources with more min-entropy and with more error. -/
theorem IsExtractor.mono (h : IsExtractor ext k ε) (hk : k ≤ k') (hε : ε ≤ ε') :
    IsExtractor ext k' ε' :=
  fun source hsource => (h source (hk.trans hsource)).trans hε

/-- Strong extractors remain strong extractors for sources with more min-entropy and with more
error. -/
theorem IsStrongExtractor.mono (h : IsStrongExtractor ext k ε) (hk : k ≤ k') (hε : ε ≤ ε') :
    IsStrongExtractor ext k' ε' :=
  fun source hsource => (h source (hk.trans hsource)).trans hε

omit [Fintype Output] [Nonempty Output] in
/-- Forgetting the revealed seed of a strong extractor leaves its plain output. -/
private theorem map_snd_strong (ext : Input → Seed → Output) (source : PMF Input) :
    (source.bind fun x => (PMF.uniformOfFintype Seed).map fun s => (s, ext x s)).map Prod.snd =
      (source.bind fun x => (PMF.uniformOfFintype Seed).map fun s => ext x s) := by
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- **Strong extractors are extractors**: discarding the revealed seed cannot increase statistical
distance. -/
theorem IsStrongExtractor.isExtractor (h : IsStrongExtractor ext k ε) : IsExtractor ext k ε := by
  intro source hsource
  have huniform : (PMF.uniformOfFintype (Seed × Output)).map Prod.snd =
      PMF.uniformOfFintype Output := by
    rw [← uniformOfFintype_prod, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    exact PMF.bind_const _ _ |>.trans (PMF.map_id _)
  rw [← map_snd_strong, ← huniform]
  exact (dist_map_le _ _ Prod.snd).trans (h source hsource)

variable [Fintype Input]

/-- **Extraction from `(k, δ)`-sources.** A `(k, ε)`-extractor applied to a `(k, δ)`-source gives an
output within `δ + ε` of uniform. -/
theorem IsExtractor.dist_le_of_isSource (h : IsExtractor ext k ε) {source : PMF Input}
    {δ : ℝ≥0} (hsource : IsSource source k δ) :
    dist (source.bind fun x => (PMF.uniformOfFintype Seed).map fun s => ext x s)
      (PMF.uniformOfFintype Output) ≤ δ + ε := by
  obtain ⟨close, hclose, hdist⟩ := hsource
  refine (dist_triangle _
    (close.bind fun x => (PMF.uniformOfFintype Seed).map fun s => ext x s) _).trans
    (add_le_add ?_ (h close hclose))
  exact (dist_bind_le source close _).trans hdist

/-- **Strong extraction from `(k, δ)`-sources.** A strong `(k, ε)`-extractor applied to a
`(k, δ)`-source gives a seed and output within `δ + ε` of a uniform pair. -/
theorem IsStrongExtractor.dist_le_of_isSource (h : IsStrongExtractor ext k ε)
    {source : PMF Input} {δ : ℝ≥0} (hsource : IsSource source k δ) :
    dist (source.bind fun x => (PMF.uniformOfFintype Seed).map fun s => (s, ext x s))
      (PMF.uniformOfFintype (Seed × Output)) ≤ δ + ε := by
  obtain ⟨close, hclose, hdist⟩ := hsource
  refine (dist_triangle _
    (close.bind fun x => (PMF.uniformOfFintype Seed).map fun s => (s, ext x s)) _).trans
    (add_le_add ?_ (h close hclose))
  exact (dist_bind_le source close _).trans hdist

/-! ### Seedless extraction is impossible -/

/-- **Seedless extraction fails.** With a seed carrying no randomness, no function to `Bool` is a
`(log₂ |Input| - 1, ε)`-extractor for `ε < 1 / 2`: some output value `b` has at least half of the
inputs as preimages, and the uniform distribution on those inputs has min-entropy at least
`log₂ |Input| - 1` while its output is constantly `b`. -/
theorem not_isExtractor_bool_of_subsingleton [Nonempty Input] [Subsingleton Seed]
    (ext : Input → Seed → Bool) (hε : ε < 1 / 2) :
    ¬ IsExtractor ext (Real.logb 2 (Fintype.card Input) - 1) ε := by
  classical
  intro h
  obtain ⟨s₀⟩ := (inferInstance : Nonempty Seed)
  -- One of the two preimages of `ext · s₀` contains at least half of the inputs.
  obtain ⟨b, hb⟩ : ∃ b : Bool,
      Fintype.card Input ≤ 2 * (Finset.univ.filter fun x => ext x s₀ = b).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Input)) (fun x => ext x s₀ = true)
    simp only [Bool.not_eq_true, Finset.card_univ] at hsplit
    by_cases ht : Fintype.card Input ≤ 2 * (Finset.univ.filter fun x => ext x s₀ = true).card
    · exact ⟨true, ht⟩
    · exact ⟨false, by omega⟩
  set T := Finset.univ.filter fun x => ext x s₀ = b
  have hT : T.Nonempty := by
    rw [← Finset.card_pos]
    have := Fintype.card_pos (α := Input)
    omega
  have hentropy : Real.logb 2 (Fintype.card Input) - 1 ≤ minEntropy (uniformOfFinset T hT) := by
    rw [minEntropy_uniformOfFinset]
    have hcard : (0 : ℝ) < Fintype.card Input := by exact_mod_cast Fintype.card_pos
    have hle : (Fintype.card Input : ℝ) ≤ 2 * T.card := by exact_mod_cast hb
    have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    have hlog : Real.logb 2 (Fintype.card Input) ≤ Real.logb 2 (2 * T.card) :=
      Real.logb_le_logb_of_le (by norm_num) hcard hle
    rw [Real.logb_mul (by norm_num) hTpos.ne', Real.logb_self_eq_one (by norm_num)] at hlog
    linarith
  have hseed : PMF.uniformOfFintype Seed = PMF.pure s₀ := by
    ext s
    have hcard : Fintype.card Seed = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨s₀, fun y => Subsingleton.elim y s₀⟩
    rw [Subsingleton.elim s s₀]
    simp [hcard]
  have hconst : ((uniformOfFinset T hT).bind fun x =>
      (PMF.uniformOfFintype Seed).map fun s => ext x s) = PMF.pure b := by
    simp only [hseed, PMF.pure_map]
    ext b'
    rw [PMF.bind_apply]
    calc
      ∑' x, (uniformOfFinset T hT) x * PMF.pure (ext x s₀) b' =
          ∑' x, (uniformOfFinset T hT) x * PMF.pure b b' := tsum_congr fun x => by
        by_cases hx : x ∈ T
        · rw [(Finset.mem_filter.mp hx).2]
        · rw [(PMF.apply_eq_zero_iff _ x).mpr (by rwa [mem_support_uniformOfFinset_iff]),
            zero_mul, zero_mul]
      _ = PMF.pure b b' := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hdist := h _ hentropy
  rw [hconst, dist_uniformOfFintype_bool] at hdist
  cases b <;> norm_num at hdist <;> linarith

end Cslib.Probability
