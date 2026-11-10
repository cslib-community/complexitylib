/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Extractor.Basic
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Foundations.BooleanAnalysis.HadamardRectangles
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.StatisticalDistance

/-!
# Two-source extractors and the Chor–Goldreich theorem

A *two-source extractor* `ext : X → Y → Output` needs no seed: applied to independent samples of
two sources with min-entropy at least `k₁` and `k₂`, its output is within statistical distance `ε`
of uniform (`Cslib.Probability.IsTwoSourceExtractor`). It is *strong in the second source* if the
output stays `ε`-close to uniform even when the second sample is revealed
(`Cslib.Probability.IsStrongTwoSourceExtractor`) [Chor and Goldreich][ChorGoldreich1988],
[Vadhan, Chapter 6][Vadhan2012].

**Chor–Goldreich.** The inner product modulo two of two bit strings of length `n` is a strong
two-source extractor with error `2 ^ ((n - k₁ - k₂) / 2) / 2`
(`isStrongTwoSourceExtractor_dotProduct`, `isTwoSourceExtractor_dotProduct`), from the average
bias bound `sum_mul_abs_bias_dotProduct_le`. The error is below `1 / 2` once `k₁ + k₂ > n` and
decays exponentially in `k₁ + k₂ - n` [Chor and Goldreich, Theorem 9][ChorGoldreich1988].

The statistical distance of a bit from uniform is half its bias `|𝔼 (-1)^b|`
(`dist_map_uniformOfFintype_bool`). Given the revealed `y`, the bias of `x ⬝ᵥ y` is a Hadamard
transform of the distribution `p` of `x`. By Cauchy–Schwarz over `y` and Parseval's identity for
the Hadamard transform (`BitString.sum_sq_sum_mul_signVal_dotProduct`), the average bias is at
most `√(2 ^ n ‖p‖² ‖q‖²)`, and a source of min-entropy `k` has `‖p‖² ≤ 2 ^ (-k)`. The argument
applies to every source directly, without decomposing it into flat sources.

The threshold `k₁ + k₂ > n` cannot be lowered to `k₁ + k₂ = n`: strings supported on a set `S` of
coordinates and strings supported on its complement are orthogonal, so the inner product of
uniform samples of the two is constant (`exists_minEntropy_bind_dotProduct_eq_pure`,
`not_isTwoSourceExtractor_dotProduct`).

## Main definitions

* `Cslib.Probability.IsTwoSourceExtractor`: two-source extractors.
* `Cslib.Probability.IsStrongTwoSourceExtractor`: two-source extractors that are strong in the
  second source.

## Main results

* `Cslib.Probability.IsStrongTwoSourceExtractor.isTwoSourceExtractor`: strong two-source
  extractors are two-source extractors.
* `Cslib.Probability.dist_map_uniformOfFintype_bool`: distance of a bit from uniform is half its
  bias.
* `Cslib.Probability.sum_mul_abs_bias_dotProduct_le`: the Chor–Goldreich bias bound.
* `Cslib.Probability.isStrongTwoSourceExtractor_dotProduct`,
  `Cslib.Probability.isTwoSourceExtractor_dotProduct`: the Chor–Goldreich theorem.
* `Cslib.Probability.exists_minEntropy_bind_dotProduct_eq_pure`,
  `Cslib.Probability.not_isTwoSourceExtractor_dotProduct`: the inner product does not extract from
  sources with `k₁ + k₂ = n`.

## References

* [B. Chor and O. Goldreich, *Unbiased bits from sources of weak randomness and probabilistic
  communication complexity*][ChorGoldreich1988]
* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Chapter 6
-/

@[expose] public section

namespace Cslib.Probability

open Cslib.Probability.PMF Finset

variable {X Y Output : Type*} [Fintype Output] [Nonempty Output]

/-- A **two-source `(k₁, k₂, ε)`-extractor**: for independent sources of min-entropy at least `k₁`
and `k₂`, applying `ext` to independent samples gives an output within statistical distance `ε` of
uniform. -/
def IsTwoSourceExtractor (ext : X → Y → Output) (k₁ k₂ ε : ℝ) : Prop :=
  ∀ (p : PMF X) (q : PMF Y), k₁ ≤ minEntropy p → k₂ ≤ minEntropy q →
    dist (p.bind fun x => q.map fun y => ext x y) (PMF.uniformOfFintype Output) ≤ ε

/-- A two-source `(k₁, k₂, ε)`-extractor that is **strong in the second source**: for independent
sources of min-entropy at least `k₁` and `k₂`, the second sample paired with the output is within
statistical distance `ε` of the second sample paired with an independent uniform output. -/
def IsStrongTwoSourceExtractor [Fintype Y] (ext : X → Y → Output) (k₁ k₂ ε : ℝ) : Prop :=
  ∀ (p : PMF X) (q : PMF Y), k₁ ≤ minEntropy p → k₂ ≤ minEntropy q →
    dist (q.bind fun y => p.map fun x => (y, ext x y))
      (q.bind fun y => (PMF.uniformOfFintype Output).map fun z => (y, z)) ≤ ε

variable {ext : X → Y → Output} {k₁ k₂ k₁' k₂' ε ε' : ℝ}

/-- Two-source extractors remain two-source extractors for sources with more min-entropy and with
more error. -/
theorem IsTwoSourceExtractor.mono (h : IsTwoSourceExtractor ext k₁ k₂ ε) (hk₁ : k₁ ≤ k₁')
    (hk₂ : k₂ ≤ k₂') (hε : ε ≤ ε') : IsTwoSourceExtractor ext k₁' k₂' ε' :=
  fun p q hp hq => (h p q (hk₁.trans hp) (hk₂.trans hq)).trans hε

/-- Strong two-source extractors remain strong for sources with more min-entropy and with more
error. -/
theorem IsStrongTwoSourceExtractor.mono [Fintype Y] (h : IsStrongTwoSourceExtractor ext k₁ k₂ ε)
    (hk₁ : k₁ ≤ k₁') (hk₂ : k₂ ≤ k₂') (hε : ε ≤ ε') : IsStrongTwoSourceExtractor ext k₁' k₂' ε' :=
  fun p q hp hq => (h p q (hk₁.trans hp) (hk₂.trans hq)).trans hε

/-- **Strong two-source extractors are two-source extractors**: forgetting the revealed second
sample cannot increase statistical distance. -/
theorem IsStrongTwoSourceExtractor.isTwoSourceExtractor [Fintype Y]
    (h : IsStrongTwoSourceExtractor ext k₁ k₂ ε) : IsTwoSourceExtractor ext k₁ k₂ ε := by
  intro p q hp hq
  have hleft : (q.bind fun y => p.map fun x => (y, ext x y)).map Prod.snd =
      p.bind fun x => q.map fun y => ext x y := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    simpa only [PMF.map, Function.comp_def] using
      PMF.bind_comm q p (fun y x => PMF.pure (ext x y))
  have hright : (q.bind fun y => (PMF.uniformOfFintype Output).map fun z => (y, z)).map
      Prod.snd = PMF.uniformOfFintype Output := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    exact (PMF.bind_const _ _).trans (PMF.map_id _)
  rw [← hleft, ← hright]
  exact (dist_map_le _ _ Prod.snd).trans (h p q hp hq)

/-! ### The bias of a bit -/

open BitString in
/-- **Statistical distance of a bit from uniform is half its bias**: for a bit `f a` computed from
a sample `a` of `p`, the distance from a uniform bit is `|𝔼 (-1)^{f a}| / 2`. -/
theorem dist_map_uniformOfFintype_bool {α : Type*} [Fintype α] (p : PMF α) (f : α → Bool) :
    dist (p.map f) (PMF.uniformOfFintype Bool) = |∑ a, (p a).toReal * signVal (f a)| / 2 := by
  rw [dist_uniformOfFintype_bool, map_apply_toReal]
  have hsign : ∑ a, (p a).toReal * signVal (f a) =
      1 - 2 * ∑ a, if true = f a then (p a).toReal else 0 := by
    rw [mul_sum, ← sum_toReal p, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    cases f a <;> simp [signVal]; ring
  rw [hsign, show (1 : ℝ) - 2 * ∑ a, (if true = f a then (p a).toReal else 0) =
    -(2 * ((∑ a, if true = f a then (p a).toReal else 0) - 1 / 2)) by ring, abs_neg, abs_mul,
    abs_two]
  ring

/-! ### The Chor–Goldreich theorem -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum of squared probabilities of a source of min-entropy at least `k` is at most `2⁻ᵏ`. -/
private theorem sum_sq_le_of_le_minEntropy {α : Type*} [Fintype α] {p : PMF α} {k : ℝ}
    (hp : k ≤ minEntropy p) : ∑ a, (p a).toReal ^ 2 ≤ 2 ^ (-k) := by
  rw [← collisionProbability_eq_sum]
  exact (collisionProbability_le_rpow_neg_minEntropy p).trans
    (Real.rpow_le_rpow_of_exponent_le one_le_two (neg_le_neg hp))

open BitString in
/-- **The Chor–Goldreich bias bound.** For independent sources `p` and `q` of bit strings indexed
by `ι`, with `n = |ι|` and min-entropy at least `k₁` and `k₂`, the bias `|𝔼ₓ (-1)^{x ⬝ᵥ y}|` of the
inner product, averaged over `y` drawn from `q`, is at most `2 ^ ((n - k₁ - k₂) / 2)`. -/
theorem sum_mul_abs_bias_dotProduct_le {p q : PMF (ι → Bool)} (hp : k₁ ≤ minEntropy p)
    (hq : k₂ ≤ minEntropy q) :
    ∑ y, (q y).toReal * |∑ x, (p x).toReal * signVal (x ⬝ᵥ y)| ≤
      2 ^ ((Fintype.card ι - k₁ - k₂) / 2) := by
  set c : (ι → Bool) → ℝ := fun y => ∑ x, (p x).toReal * signVal (x ⬝ᵥ y)
  have hsq : (∑ y, (q y).toReal * |c y|) ^ 2 ≤
      (2 ^ ((Fintype.card ι - k₁ - k₂) / 2)) ^ 2 := by
    calc
      (∑ y, (q y).toReal * |c y|) ^ 2 ≤ (∑ y, (q y).toReal ^ 2) * ∑ y, |c y| ^ 2 :=
        sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ y, (q y).toReal ^ 2) * (2 ^ Fintype.card ι * ∑ x, (p x).toReal ^ 2) := by
        simp only [sq_abs, c]
        rw [sum_sq_sum_mul_signVal_dotProduct]
      _ ≤ 2 ^ (-k₂) * (2 ^ Fintype.card ι * 2 ^ (-k₁)) := by
        gcongr
        · exact sum_sq_le_of_le_minEntropy hq
        · exact sum_sq_le_of_le_minEntropy hp
      _ = (2 ^ ((Fintype.card ι - k₁ - k₂) / 2)) ^ 2 := by
        rw [← Real.rpow_natCast (2 : ℝ) (Fintype.card ι), ← Real.rpow_natCast _ 2,
          ← Real.rpow_mul zero_le_two, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
        congr 1
        push_cast
        ring
  exact (pow_le_pow_iff_left₀ (sum_nonneg fun y _ => mul_nonneg ENNReal.toReal_nonneg
    (abs_nonneg _)) (by positivity) two_ne_zero).mp hsq

/-- **The Chor–Goldreich theorem, strong form.** The inner product modulo two of bit strings
indexed by `ι`, with `n = |ι|`, is a two-source extractor strong in the second source: for
independent sources of min-entropy at least `k₁` and `k₂`, revealing the second sample leaves the
inner product within statistical distance `2 ^ ((n - k₁ - k₂) / 2) / 2` of a uniform bit. -/
theorem isStrongTwoSourceExtractor_dotProduct (k₁ k₂ : ℝ) :
    IsStrongTwoSourceExtractor (fun x y : ι → Bool => x ⬝ᵥ y) k₁ k₂
      (2 ^ ((Fintype.card ι - k₁ - k₂) / 2) / 2) := by
  intro p q hp hq
  have hpair (y : ι → Bool) :
      (p.map fun x => (y, x ⬝ᵥ y)) = (p.map fun x => x ⬝ᵥ y).map fun z => (y, z) := by
    rw [PMF.map_comp]
    rfl
  simp only [hpair]
  rw [dist_bind_pair]
  simp only [dist_map_uniformOfFintype_bool, mul_div_assoc', ← sum_div]
  gcongr
  exact sum_mul_abs_bias_dotProduct_le hp hq

omit [DecidableEq ι] in
/-- **The Chor–Goldreich theorem.** The inner product modulo two of bit strings indexed by `ι`,
with `n = |ι|`, is a two-source extractor for min-entropies `k₁` and `k₂` with error
`2 ^ ((n - k₁ - k₂) / 2) / 2`. -/
theorem isTwoSourceExtractor_dotProduct (k₁ k₂ : ℝ) :
    IsTwoSourceExtractor (fun x y : ι → Bool => x ⬝ᵥ y) k₁ k₂
      (2 ^ ((Fintype.card ι - k₁ - k₂) / 2) / 2) := by
  classical
  exact (isStrongTwoSourceExtractor_dotProduct k₁ k₂).isTwoSourceExtractor

/-! ### The entropy threshold is necessary -/

/-- The bit strings that vanish outside `S`. -/
private def supportedOn (S : Finset ι) : Finset (ι → Bool) :=
  univ.image fun (z : S → Bool) i => if h : i ∈ S then z ⟨i, h⟩ else false

private theorem supportedOn_nonempty (S : Finset ι) : (supportedOn S).Nonempty :=
  univ_nonempty.image _

private theorem eq_false_of_mem_supportedOn {S : Finset ι} {x : ι → Bool}
    (hx : x ∈ supportedOn S) {i : ι} (hi : i ∉ S) : x i = false := by
  obtain ⟨z, -, rfl⟩ := mem_image.mp hx
  simp [hi]

private theorem card_supportedOn (S : Finset ι) : (supportedOn S).card = 2 ^ S.card := by
  rw [supportedOn, card_image_of_injective, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe]
  intro z z' h
  funext ⟨i, hi⟩
  simpa [hi] using congrFun h i

private theorem minEntropy_uniformOfFinset_supportedOn (S : Finset ι) :
    minEntropy (uniformOfFinset (supportedOn S) (supportedOn_nonempty S)) = S.card := by
  rw [minEntropy_uniformOfFinset, card_supportedOn, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one one_lt_two, mul_one]

/-- **Orthogonal sources.** For every set `S` of coordinates, the uniform distributions on the
strings vanishing outside `S` and on those vanishing on `S` have min-entropy `|S|` and `|Sᶜ|`, whose
sum is `n`, yet the inner product of independent samples is always `false`. -/
theorem exists_minEntropy_bind_dotProduct_eq_pure (S : Finset ι) :
    ∃ p q : PMF (ι → Bool), minEntropy p = S.card ∧ minEntropy q = Sᶜ.card ∧
      (p.bind fun x => q.map fun y => x ⬝ᵥ y) = PMF.pure false := by
  refine ⟨uniformOfFinset (supportedOn S) (supportedOn_nonempty S),
    uniformOfFinset (supportedOn Sᶜ) (supportedOn_nonempty Sᶜ),
    minEntropy_uniformOfFinset_supportedOn S, minEntropy_uniformOfFinset_supportedOn Sᶜ, ?_⟩
  have horth : ∀ x ∈ supportedOn S, ∀ y ∈ supportedOn Sᶜ, x ⬝ᵥ y = false := by
    intro x hx y hy
    refine sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ S
    · rw [eq_false_of_mem_supportedOn hy (by simpa using hi)]
      exact mul_zero (x i)
    · rw [eq_false_of_mem_supportedOn hx hi]
      exact zero_mul (y i)
  refine (bind_congr_on_support _ _ (fun _ => PMF.pure false) fun x hx => ?_).trans
    (PMF.bind_const _ _)
  refine (map_congr_on_support _ _ (fun _ => false) fun y hy => ?_).trans (PMF.map_const _ _)
  rw [mem_support_uniformOfFinset_iff] at hx hy
  exact horth x hx y hy

/-- **The threshold `k₁ + k₂ > n` is necessary.** For every set `S` of coordinates, the inner
product is not a two-source extractor for min-entropies `|S|` and `|Sᶜ|`, which sum to `n`, with
error less than `1 / 2` (`exists_minEntropy_bind_dotProduct_eq_pure`). -/
theorem not_isTwoSourceExtractor_dotProduct (S : Finset ι) (hε : ε < 1 / 2) :
    ¬ IsTwoSourceExtractor (fun x y : ι → Bool => x ⬝ᵥ y) S.card Sᶜ.card ε := by
  intro h
  obtain ⟨p, q, hp, hq, hconst⟩ := exists_minEntropy_bind_dotProduct_eq_pure S
  have hdist := h p q hp.ge hq.ge
  rw [hconst, dist_uniformOfFintype_bool] at hdist
  norm_num at hdist
  linarith

end Cslib.Probability
