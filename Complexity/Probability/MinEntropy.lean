/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Collision
public import Complexity.Probability.Entropy
import Complexity.Probability.PMF.Event
import Complexity.Probability.StatisticalDistance

/-!
# Min-entropy and weak random sources

The min-entropy of a distribution is the least information content `-log₂ p(a)` of a possible
outcome, measured in bits like `Cslib.Probability.PMF.entropy`. A distribution has min-entropy at
least `k` exactly when every outcome has probability at most `2⁻ᵏ` (`le_minEntropy_iff`); such a
distribution is called a `k`-source. A `(k, ε)`-source is within statistical distance `ε` of a
`k`-source. These are the weak random sources from which randomness extractors produce nearly
uniform bits [Chor, Goldreich][ChorGoldreich1988], [Vadhan, Chapter 6][Vadhan2012].

Min-entropy never exceeds Shannon entropy and bounds the collision probability. A mixture of
`k`-sources is a `k`-source; conversely, every `k`-source is a mixture of flat `k`-sources
(`Cslib.Probability.PMF.exists_eq_bind_uniformOfFinset_of_le_minEntropy`). Discarding rare heavy
outcomes turns a distribution into a `(k, ε)`-source (`isSource_of_heavy_le`).

## Main definitions

* `Cslib.Probability.PMF.minEntropy`: min-entropy in bits.
* `Cslib.Probability.PMF.IsSource`: `(k, ε)`-sources.

## Main results

* `Cslib.Probability.PMF.le_minEntropy_iff`: min-entropy at least `k` means every outcome has
  probability at most `2⁻ᵏ`.
* `Cslib.Probability.PMF.minEntropy_le_entropy`: min-entropy is at most Shannon entropy.
* `Cslib.Probability.PMF.minEntropy_uniformOfFinset`: a flat distribution on `K` outcomes has
  min-entropy `log₂ K`.
* `Cslib.Probability.PMF.le_minEntropy_bind`: a mixture of `k`-sources is a `k`-source.
* `Cslib.Probability.PMF.collisionProbability_le_rpow_neg_minEntropy`: collision probability is
  at most `2^(-H∞)`.
* `Cslib.Probability.PMF.isSource_zero_iff`: a `(k, 0)`-source is a `k`-source.
* `Cslib.Probability.PMF.isSource_of_heavy_le`: discarding rare heavy outcomes gives a
  `(k, ε)`-source.

## References

* [B. Chor, O. Goldreich, *Unbiased Bits from Sources of Weak Randomness and Probabilistic
  Communication Complexity*][ChorGoldreich1988]
* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Chapter 6
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped NNReal

variable {α β : Type*}

/-! ### Min-entropy -/

/-- Min-entropy in bits: the least information content `-log₂ p(a)` of a possible outcome `a`.
Its lower bounds are upper bounds on the outcome probabilities (`le_minEntropy_iff`). -/
noncomputable def minEntropy (p : PMF α) : ℝ := ⨅ a : p.support, surprisal p a

/-- On the support, a lower information bound is exactly an upper probability bound. -/
theorem le_surprisal_iff_mass_le (p : PMF α) {a : α} (ha : a ∈ p.support) {k : ℝ} :
    k ≤ surprisal p a ↔ (p a).toReal ≤ 2 ^ (-k) := by
  rw [surprisal, le_neg, Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (ENNReal.toReal_pos ha (PMF.apply_ne_top _ _))]

private theorem bddBelow_surprisal (p : PMF α) :
    BddBelow (Set.range fun a : p.support => surprisal p a) :=
  ⟨0, by rintro _ ⟨a, rfl⟩; exact surprisal_nonneg p a⟩

/-- Min-entropy is at most the information content of every possible outcome. -/
theorem minEntropy_le_surprisal (p : PMF α) {a : α} (ha : a ∈ p.support) :
    minEntropy p ≤ surprisal p a :=
  ciInf_le (bddBelow_surprisal p) ⟨a, ha⟩

/-- Min-entropy is nonnegative. -/
theorem minEntropy_nonneg (p : PMF α) : 0 ≤ minEntropy p :=
  Real.iInf_nonneg fun a => surprisal_nonneg p a

/-- **Min-entropy lower bounds.** A distribution has min-entropy at least `k` exactly when every
outcome has probability at most `2⁻ᵏ`. -/
theorem le_minEntropy_iff (p : PMF α) {k : ℝ} :
    k ≤ minEntropy p ↔ ∀ a, (p a).toReal ≤ 2 ^ (-k) := by
  have : Nonempty p.support := p.support_nonempty.to_subtype
  rw [minEntropy, le_ciInf_iff (bddBelow_surprisal p)]
  constructor
  · intro h a
    by_cases ha : a ∈ p.support
    · exact (le_surprisal_iff_mass_le p ha).mp (h ⟨a, ha⟩)
    · rw [(p.apply_eq_zero_iff a).mpr ha, ENNReal.toReal_zero]
      positivity
  · rintro h ⟨a, ha⟩
    exact (le_surprisal_iff_mass_le p ha).mpr (h a)

/-- Every outcome has probability at most `2` to the power of minus the min-entropy. -/
theorem toReal_apply_le_rpow_neg_minEntropy (p : PMF α) (a : α) :
    (p a).toReal ≤ 2 ^ (-minEntropy p) :=
  (le_minEntropy_iff p).mp le_rfl a

/-- Collision probability is at most `2` to the power of minus the min-entropy. -/
theorem collisionProbability_le_rpow_neg_minEntropy (p : PMF α) :
    collisionProbability p ≤ 2 ^ (-minEntropy p) :=
  collisionProbability_le_of_mass_le p (toReal_apply_le_rpow_neg_minEntropy p)

/-- On a finite type the least information content is attained by some possible outcome. -/
theorem exists_surprisal_eq_minEntropy [Finite α] (p : PMF α) :
    ∃ a ∈ p.support, surprisal p a = minEntropy p := by
  have : Nonempty p.support := p.support_nonempty.to_subtype
  obtain ⟨⟨a, ha⟩, h⟩ := exists_eq_ciInf_of_finite (f := fun a : p.support => surprisal p a)
  exact ⟨a, ha, h⟩

/-- Min-entropy is at most Shannon entropy, which averages the information content. -/
theorem minEntropy_le_entropy [Finite α] (p : PMF α) : minEntropy p ≤ entropy p := by
  let := Fintype.ofFinite α
  rw [entropy_eq_sum_surprisal]
  calc
    minEntropy p = ∑ a, (p a).toReal * minEntropy p := by
      rw [← Finset.sum_mul, sum_toReal, one_mul]
    _ ≤ ∑ a, (p a).toReal * surprisal p a := by
      refine Finset.sum_le_sum fun a _ => ?_
      by_cases ha : a ∈ p.support
      · exact mul_le_mul_of_nonneg_left (minEntropy_le_surprisal p ha) ENNReal.toReal_nonneg
      · rw [(p.apply_eq_zero_iff a).mpr ha, ENNReal.toReal_zero, zero_mul, zero_mul]

/-- Min-entropy is at most the logarithm of the size of a finite type. -/
theorem minEntropy_le_logb_card [Fintype α] (p : PMF α) :
    minEntropy p ≤ Real.logb 2 (Fintype.card α) :=
  (minEntropy_le_entropy p).trans (entropy_le_log_card p)

/-- The uniform distribution on a nonempty finite set `s` has min-entropy `log₂ |s|`. -/
theorem minEntropy_uniformOfFinset (s : Finset α) (hs : s.Nonempty) :
    minEntropy (uniformOfFinset s hs) = Real.logb 2 s.card := by
  classical
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hmass : (2 : ℝ) ^ (-Real.logb 2 s.card) = (s.card : ℝ)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hcard]
  obtain ⟨a, ha⟩ := id hs
  apply le_antisymm
  · have hsupport : a ∈ (uniformOfFinset s hs).support :=
      (mem_support_uniformOfFinset_iff hs a).mpr ha
    refine (minEntropy_le_surprisal _ hsupport).trans_eq ?_
    rw [surprisal, uniformOfFinset_apply, ite_eq_left ha, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, Real.logb_inv, neg_neg]
  · rw [le_minEntropy_iff, hmass]
    intro b
    by_cases hb : b ∈ s
    · rw [uniformOfFinset_apply, ite_eq_left hb, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    · rw [uniformOfFinset_apply, ite_eq_right hb, ENNReal.toReal_zero]
      positivity

/-- The uniform distribution on a finite type has min-entropy the logarithm of its size. -/
@[simp] theorem minEntropy_uniformOfFintype [Fintype α] [Nonempty α] :
    minEntropy (uniformOfFintype α) = Real.logb 2 (Fintype.card α) :=
  minEntropy_uniformOfFinset _ _

/-- A deterministic value has no min-entropy. -/
@[simp] theorem minEntropy_pure (a : α) : minEntropy (PMF.pure a) = 0 :=
  le_antisymm ((minEntropy_le_surprisal _ ((PMF.mem_support_pure_iff a a).mpr rfl)).trans_eq
    (by simp [surprisal])) (minEntropy_nonneg _)

/-- **Mixtures of `k`-sources are `k`-sources.** If every possible component of a mixture has
min-entropy at least `k`, so does the mixture. -/
theorem le_minEntropy_bind (μ : PMF β) (f : β → PMF α) {k : ℝ}
    (h : ∀ b ∈ μ.support, k ≤ minEntropy (f b)) : k ≤ minEntropy (μ.bind f) := by
  rw [le_minEntropy_iff]
  intro a
  have hk : (0 : ℝ) ≤ 2 ^ (-k) := by positivity
  have hcomponent (b : β) : μ b * f b a ≤ μ b * ENNReal.ofReal (2 ^ (-k)) := by
    by_cases hb : b ∈ μ.support
    · gcongr
      exact (ENNReal.le_ofReal_iff_toReal_le (PMF.apply_ne_top _ _) hk).mpr
        ((le_minEntropy_iff (f b)).mp (h b hb) a)
    · simp [(μ.apply_eq_zero_iff b).mpr hb]
  apply ENNReal.toReal_le_of_le_ofReal hk
  calc
    μ.bind f a = ∑' b, μ b * f b a := PMF.bind_apply μ f a
    _ ≤ ∑' b, μ b * ENNReal.ofReal (2 ^ (-k)) := tsum_le_tsum hcomponent
    _ = ENNReal.ofReal (2 ^ (-k)) := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-! ### Weak random sources -/

/-- A `(k, ε)`-source: a distribution within statistical distance `ε` of one with min-entropy at
least `k`. A `k`-source is a `(k, 0)`-source (`isSource_zero_iff`). -/
def IsSource [Fintype α] (p : PMF α) (k : ℝ) (ε : ℝ≥0) : Prop :=
  ∃ q : PMF α, k ≤ minEntropy q ∧ StatisticallyClose p q ε

/-- A `(k, 0)`-source is exactly a distribution of min-entropy at least `k`. -/
@[simp] theorem isSource_zero_iff [Fintype α] (p : PMF α) {k : ℝ} :
    IsSource p k 0 ↔ k ≤ minEntropy p := by
  constructor
  · rintro ⟨q, hq, hclose⟩
    rwa [(statisticallyClose_zero_iff p q).mp hclose]
  · exact fun h => ⟨p, h, StatisticallyClose.refl p⟩

/-- A distribution of min-entropy at least `k` is a `(k, ε)`-source for every `ε`. -/
theorem isSource_of_le_minEntropy [Fintype α] {p : PMF α} {k : ℝ} (h : k ≤ minEntropy p)
    (ε : ℝ≥0) : IsSource p k ε :=
  ⟨p, h, StatisticallyClose.mono (zero_le (a := ε)) (StatisticallyClose.refl p)⟩

/-- Sources remain sources with less min-entropy and more error. -/
theorem IsSource.mono [Fintype α] {p : PMF α} {k k' : ℝ} {ε ε' : ℝ≥0}
    (h : IsSource p k ε) (hk : k' ≤ k) (hε : ε ≤ ε') : IsSource p k' ε' :=
  let ⟨q, hq, hclose⟩ := h
  ⟨q, hk.trans hq, StatisticallyClose.mono hε hclose⟩

/-- A distribution `δ`-close to a `(k, ε)`-source is a `(k, δ + ε)`-source. -/
theorem IsSource.of_statisticallyClose [Fintype α] {p q : PMF α} {k : ℝ} {ε δ : ℝ≥0}
    (h : IsSource q k ε) (hpq : StatisticallyClose p q δ) : IsSource p k (δ + ε) :=
  let ⟨r, hr, hclose⟩ := h
  ⟨r, hr, hpq.trans hclose⟩

/-- **Smoothing by discarding heavy outcomes.** If the outcomes of probability more than `2⁻ᵏ`
have total probability at most `δ < 1`, the distribution is a `(k + log₂ (1 - δ), δ)`-source.
Conditioning on the light outcomes moves it by the discarded probability and multiplies each
remaining mass by at most `1 / (1 - δ)`. For `δ ≤ 1 / 2` the min-entropy loss is at most one bit. -/
theorem isSource_of_heavy_le [Fintype α] (p : PMF α) {k : ℝ} {δ : ℝ≥0} (hδ : (δ : ℝ) < 1)
    (hheavy : (p.toOuterMeasure {a | 2 ^ (-k) < (p a).toReal}).toReal ≤ δ) :
    IsSource p (k + Real.logb 2 (1 - δ)) δ := by
  let light := {a | (p a).toReal ≤ 2 ^ (-k)}
  have hpartition : (p.toOuterMeasure light).toReal +
      (p.toOuterMeasure {a | 2 ^ (-k) < (p a).toReal}).toReal = 1 := by
    simpa only [light, Set.compl_ofPred, not_le] using toOuterMeasure_toReal_add_compl p light
  have hlight : 1 - δ ≤ (p.toOuterMeasure light).toReal := by linarith
  have hevent := (toOuterMeasure_toReal_pos_iff p light).mp (by linarith)
  refine ⟨p.filter light hevent, (le_minEntropy_iff _).mpr fun a => ?_, ?_⟩
  · rw [filter_apply_toReal]
    split_ifs with ha
    · rw [neg_add, Real.rpow_add two_pos, Real.rpow_neg zero_le_two (Real.logb 2 (1 - δ)),
        Real.rpow_logb two_pos (by norm_num) (by linarith), ← div_eq_mul_inv]
      exact div_le_div₀ (by positivity) ha (by linarith) hlight
    · positivity
  · rw [StatisticallyClose, dist_filter]
    simpa only [light, Set.compl_ofPred, not_le] using hheavy

end Cslib.Probability.PMF
