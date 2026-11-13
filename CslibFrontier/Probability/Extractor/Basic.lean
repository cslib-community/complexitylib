/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MinEntropy
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Probability.Product
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
* `Cslib.Probability.exists_minEntropy_map_eq_pure_bool`: a reusable Boolean-fiber witness.
* `Cslib.Probability.exists_minEntropy_map_first_eq_pure`: positive-length bit-string witness,
  fixed first output coordinate and distance at least `1 / 2` (Arora–Barak draft, exercise 16.7).
* `Cslib.Probability.not_isExtractor_bitString`: the immediate multibit non-extractor consequence.
* `Cslib.Probability.not_isExtractor_bool_of_subsingleton`: seedless extraction of one bit fails
  for sources missing one bit of min-entropy.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07],
  January 8, 2007 draft, Chapter 16, Exercise 7
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

/-- A Boolean map has a flat source missing at most one bit of entropy on which it is constant. -/
theorem exists_minEntropy_map_eq_pure_bool [Nonempty Input] (f : Input → Bool) :
    ∃ (source : PMF Input) (b : Bool),
      Real.logb 2 (Fintype.card Input) - 1 ≤ minEntropy source ∧
      source.map f = PMF.pure b := by
  classical
  -- One of the two preimages of `f` contains at least half of the inputs.
  obtain ⟨b, hb⟩ : ∃ b : Bool,
      Fintype.card Input ≤ 2 * (Finset.univ.filter fun x => f x = b).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Input)) (fun x => f x = true)
    simp only [Bool.not_eq_true, Finset.card_univ] at hsplit
    by_cases ht : Fintype.card Input ≤ 2 * (Finset.univ.filter fun x => f x = true).card
    · exact ⟨true, ht⟩
    · exact ⟨false, by omega⟩
  set T := Finset.univ.filter fun x => f x = b
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
  refine ⟨uniformOfFinset T hT, b, hentropy, ?_⟩
  rw [PMF.map]
  ext b'
  rw [PMF.bind_apply]
  calc
    ∑' x, (uniformOfFinset T hT) x * PMF.pure (f x) b' =
        ∑' x, (uniformOfFinset T hT) x * PMF.pure b b' := tsum_congr fun x => by
      by_cases hx : x ∈ T
      · rw [(Finset.mem_filter.mp hx).2]
      · rw [(PMF.apply_eq_zero_iff _ x).mpr (by rwa [mem_support_uniformOfFinset_iff]),
          zero_mul, zero_mul]
    _ = PMF.pure b b' := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

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
  obtain ⟨source, b, hentropy, hmap⟩ := exists_minEntropy_map_eq_pure_bool (fun x => ext x s₀)
  have hseed : PMF.uniformOfFintype Seed = PMF.pure s₀ := by
    ext s
    have hcard : Fintype.card Seed = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨s₀, fun y => Subsingleton.elim y s₀⟩
    rw [Subsingleton.elim s s₀]
    simp [hcard]
  have hconst : (source.bind fun x =>
      (PMF.uniformOfFintype Seed).map fun s => ext x s) = PMF.pure b := by
    simpa only [hseed, PMF.map, PMF.pure_bind, Function.comp_def] using hmap
  have hdist := h _ hentropy
  rw [hconst, dist_uniformOfFintype_bool] at hdist
  cases b <;> norm_num at hdist <;> linarith

/-- Explicit seedless impossibility on bit strings: a source of real min-entropy at least
`n - 1` fixes the first output bit and has output distance at least `1 / 2` from uniform.
This is [AroraBarak07], Chapter 16, §7 (printed page 319), with first coordinate indexed by
zero in Lean. Both lengths are positive; there is no efficiency assumption. -/
theorem exists_minEntropy_map_first_eq_pure {n m : ℕ} (_hn : 1 ≤ n) (hm : 1 ≤ m)
    (f : BitString n → BitString m) :
    ∃ (source : PMF (BitString n)) (b : Bool),
      (n : ℝ) - 1 ≤ minEntropy source ∧
      (source.map f).map (fun y => y ⟨0, hm⟩) = PMF.pure b ∧
      1 / 2 ≤ dist (source.map f) (PMF.uniformOfFintype (BitString m)) := by
  obtain ⟨source, b, hentropy, hmap⟩ :=
    exists_minEntropy_map_eq_pure_bool (fun x => f x ⟨0, hm⟩)
  have hcard : Real.logb 2 (Fintype.card (BitString n)) = n := by
    simp [Real.logb_pow, Real.logb_self_eq_one]
  rw [hcard] at hentropy
  have hfirst : (source.map f).map (fun y => y ⟨0, hm⟩) = PMF.pure b := by
    simpa only [PMF.map_comp, Function.comp_def] using hmap
  refine ⟨source, b, hentropy, hfirst, ?_⟩
  have huniform : (PMF.uniformOfFintype (BitString m)).map (fun y => y ⟨0, hm⟩) =
      PMF.uniformOfFintype Bool := by
    rw [← pi_uniformOfFintype, pi_map_eval]
  have hdist := dist_map_le (source.map f) (PMF.uniformOfFintype (BitString m))
    (fun y => y ⟨0, hm⟩)
  rw [hfirst, huniform, dist_uniformOfFintype_bool] at hdist
  cases b <;> norm_num at hdist ⊢ <;> exact hdist

/-- With a singleton seed, no positive-length bit-string map extracts at error below `1 / 2`
from all sources of min-entropy at least the real number `n - 1`. -/
theorem not_isExtractor_bitString {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (f : BitString n → BitString m) (hε : ε < 1 / 2) :
    ¬ IsExtractor (fun x (_ : Unit) => f x) ((n : ℝ) - 1) ε := by
  intro h
  obtain ⟨source, b, hentropy, _, hdist⟩ := exists_minEntropy_map_first_eq_pure hn hm f
  have hupper := h source hentropy
  have hunit : PMF.uniformOfFintype Unit = PMF.pure () := by ext u; simp
  simp only [hunit, PMF.map, PMF.pure_bind, Function.comp_def] at hupper
  change dist (source.map f) _ ≤ ε at hupper
  linarith

end Cslib.Probability
