/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Threshold
public import CslibFrontier.Probability.PairwiseIndependent
public import CslibFrontier.Probability.Uniform
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite Goldreich–Levin decoding

The decoder samples `k` uniform base masks, forms their nonempty subset sums, and enumerates
the `2 ^ k` guesses for their inner products with the unknown string. Each guess gives one
candidate, by correcting the predictor's answers and taking a majority for each coordinate.

The bitstrings are CSLib's `Fin n → Bool`. Mathlib's Boolean ring uses XOR for addition
and AND for multiplication, so its ordinary dot product `x ⬝ᵥ r` is the required parity.
Bilinearity, pairwise independence of subset sums, and Chebyshev's inequality give an explicit
failure bound of `n / (4 * ε ^ 2 * (2 ^ k - 1))` for a predictor of agreement at least
`1 / 2 + ε`. Taking `2 ^ k - 1 ≥ n / (2 * ε ^ 2)` makes the failure probability at most one half.

This direct-coordinate variant has a larger candidate list than the sharper decoder in the
reference, but the list remains polynomial in `n` and `1 / ε` when `k` is chosen accordingly.
It avoids a separate high-agreement decoder.

These theorems concern a deterministic predictor and finite probability distributions. The
uniform PPT implementation and the hard-core reduction are separate steps. This module is
adapted from the cslib `crypto` branch at `5ff69ca`.

## Main definitions

* `nonemptySubsets`, `candidate`, `candidates`: subset masks and candidate generation.
* `agreement`: the predictor's agreement with a parity function.
* `decode`: the finite distribution of candidate sets.

## Main results

* `decode_failure_le`: the quantitative decoding guarantee.
* `decode_failure_le_half`: sufficient mask count gives success probability at least one half.
* `candidate_parity`: a perfect parity predictor recovers the target for every choice of masks.
* `card_le_of_mem_support_decode`: the candidate list has at most `2 ^ k` elements.

## References

* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
* [L. Trevisan, *CS276 Lecture 12: Goldreich–Levin*][Trevisan2009GL]. We use the subset-sum
  construction and pairwise-independent majority estimate, adapting recovery to each coordinate.

-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Probability MeasureTheory ProbabilityTheory

/-- The nonempty subsets indexing the decoder's pairwise independent masks. -/
def nonemptySubsets (k : ℕ) : Finset (Finset (Fin k)) := Finset.univ.erase ∅

/-- Every voting subset is nonempty. -/
@[simp] theorem mem_nonemptySubsets {k : ℕ} (s : Finset (Fin k)) :
    s ∈ nonemptySubsets k ↔ s.Nonempty := by
  simp [nonemptySubsets, Finset.nonempty_iff_ne_empty]

/-- There are `2 ^ k - 1` voting subsets of `k` base masks. -/
@[simp] theorem card_nonemptySubsets (k : ℕ) :
    (nonemptySubsets k).card = 2 ^ k - 1 := by
  simp [nonemptySubsets, Fintype.card_finset]

/-- Predict one coordinate using a subset mask and the guessed parities of the base masks. -/
def vote {n k : ℕ} (predictor : BitString n → Bool) (masks : Fin k → BitString n)
    (guess : BitString k) (i : Fin n) (s : Finset (Fin k)) : Bool :=
  predictor (Pi.single i 1 + ∑ j ∈ s, masks j) ^^ ∑ j ∈ s, guess j

/-- One candidate string for a particular guess of the `k` base-mask parities. -/
def candidate {n k : ℕ} (predictor : BitString n → Bool) (masks : Fin k → BitString n)
    (guess : BitString k) : BitString n :=
  fun i => BitString.strictMajorityOn (nonemptySubsets k) (vote predictor masks guess i)

/-- Enumerate all guesses of the base-mask parities and retain their candidate strings. -/
def candidates {n k : ℕ} (predictor : BitString n → Bool)
    (masks : Fin k → BitString n) : Finset (BitString n) :=
  Finset.univ.image (candidate predictor masks)

/-- Enumerating `k` guessed bits produces at most `2 ^ k` candidates. -/
theorem card_candidates_le {n k : ℕ} (predictor : BitString n → Bool)
    (masks : Fin k → BitString n) : (candidates predictor masks).card ≤ 2 ^ k := by
  calc
    _ ≤ Fintype.card (BitString k) := Finset.card_image_le
    _ = _ := by simp [BitString]

/-- With the true base-mask parities, a corrected vote is right exactly when the predictor is
right on the shifted query. This is bilinearity of the Boolean dot product. -/
theorem vote_correct_iff {n k : ℕ} (predictor : BitString n → Bool)
    (masks : Fin k → BitString n) (x : BitString n) (i : Fin n) (s : Finset (Fin k)) :
    vote predictor masks (fun j => x ⬝ᵥ masks j) i s = x i ↔
      predictor (Pi.single i 1 + ∑ j ∈ s, masks j) =
        x ⬝ᵥ (Pi.single i 1 + ∑ j ∈ s, masks j) := by
  rw [dotProduct_add, dotProduct_single_one, dotProduct_sum]
  simp only [vote, Bool.add_eq_xor]
  generalize predictor (Pi.single i 1 + ∑ j ∈ s, masks j) = a
  generalize (∑ j ∈ s, x ⬝ᵥ masks j) = b
  cases a <;> cases b <;> cases x i <;> decide

/-- The real-valued indicator that a predictor agrees with the parity of `x` on `r`. -/
def score {n : ℕ} (predictor : BitString n → Bool) (x r : BitString n) : ℝ :=
  if predictor r = x ⬝ᵥ r then 1 else 0

/-- Agreement with a parity function, averaged over a uniform query. -/
noncomputable def agreement {n : ℕ} (predictor : BitString n → Bool) (x : BitString n) : ℝ :=
  ∫ r, score predictor x r ∂(PMF.uniformOfFintype (BitString n)).toMeasure

private theorem query_uniform {n k : ℕ} (i : Fin n) (s : Finset (Fin k)) (hs : s.Nonempty) :
    (PMF.uniformOfFintype (Fin k → BitString n)).map
        (fun masks => Pi.single i 1 + ∑ j ∈ s, masks j) =
      PMF.uniformOfFintype (BitString n) := by
  change (PMF.uniformOfFintype (Fin k → BitString n)).map
    ((Equiv.addLeft (Pi.single i 1)) ∘ (fun masks => ∑ j ∈ s, masks j)) = _
  rw [← PMF.map_comp, PMF.uniformOfFintype_map_sum s hs, PMF.uniformOfFintype_map_equiv]

private theorem query_pair_uniform {n k : ℕ} (i : Fin n)
    (s t : Finset (Fin k)) (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ≠ t) :
    (PMF.uniformOfFintype (Fin k → BitString n)).map
        (fun masks => (Pi.single i 1 + ∑ j ∈ s, masks j,
          Pi.single i 1 + ∑ j ∈ t, masks j)) =
      PMF.uniformOfFintype (BitString n × BitString n) := by
  change (PMF.uniformOfFintype (Fin k → BitString n)).map
    ((Equiv.addLeft (Pi.single i 1, Pi.single i 1)) ∘
      (fun masks => (∑ j ∈ s, masks j, ∑ j ∈ t, masks j))) = _
  rw [← PMF.map_comp, PMF.uniformOfFintype_map_sum_pair s t hs ht hst,
    PMF.uniformOfFintype_map_equiv]

private theorem coordinate_error_le {n k : ℕ} (predictor : BitString n → Bool)
    (x : BitString n) (i : Fin n) (ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (h : 1 / 2 + ε ≤ agreement predictor x) :
    (PMF.uniformOfFintype (Fin k → BitString n)).toMeasure
        {masks | candidate predictor masks (fun j => x ⬝ᵥ masks j) i ≠ x i} ≤
      ENNReal.ofReal (1 / (4 * ε ^ 2 * (nonemptySubsets k).card)) := by
  let μ := (PMF.uniformOfFintype (Fin k → BitString n)).toMeasure
  let X : Finset (Fin k) → (Fin k → BitString n) → ℝ :=
    fun s masks => score predictor x (Pi.single i 1 + ∑ j ∈ s, masks j)
  have hnonempty : (nonemptySubsets k).Nonempty := by
    exact ⟨{⟨0, hk⟩}, by simp⟩
  have hmean (s : Finset (Fin k)) (hs : s ∈ nonemptySubsets k) :
      ∫ masks, X s masks ∂μ = agreement predictor x := by
    have hmap : μ.map (fun masks => Pi.single i 1 + ∑ j ∈ s, masks j) =
        (PMF.uniformOfFintype (BitString n)).toMeasure := by
      rw [PMF.toMeasure_map _ _ (measurable_of_countable _),
        query_uniform i s (mem_nonemptySubsets s |>.mp hs)]
    change (∫ masks, (score predictor x)
      ((fun masks => Pi.single i 1 + ∑ j ∈ s, masks j) masks) ∂μ) = _
    rw [← integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable, hmap]
    rfl
  have hindep : Set.Pairwise (↑(nonemptySubsets k) : Set (Finset (Fin k)))
      (fun s t => IndepFun (X s) (X t) μ) := by
    intro s hs t ht hst
    have hquery : IndepFun
        (fun masks : Fin k → BitString n => Pi.single i 1 + ∑ j ∈ s, masks j)
        (fun masks : Fin k → BitString n => Pi.single i 1 + ∑ j ∈ t, masks j) μ := by
      apply PMF.indepFun_of_map_pair _ _ _ (measurable_of_countable _) (measurable_of_countable _)
      rw [query_pair_uniform i s t (mem_nonemptySubsets s |>.mp hs)
          (mem_nonemptySubsets t |>.mp ht) hst,
        query_uniform i s (mem_nonemptySubsets s |>.mp hs),
        query_uniform i t (mem_nonemptySubsets t |>.mp ht),
        ← PMF.uniformOfFintype_prod]
    exact hquery.comp (measurable_of_countable (score predictor x))
      (measurable_of_countable (score predictor x))
  have hbound := majority_error_bound μ (nonemptySubsets k) X ε hε hnonempty
    (fun _ _ => (measurable_of_countable _).aemeasurable)
    (fun s _ => Filter.Eventually.of_forall (fun masks => by
      dsimp [X, score]
      split <;> norm_num))
    hindep (fun s hs => by rw [hmean s hs]; exact h)
  apply le_trans (measure_mono ?_) hbound
  intro masks herror
  have hmajority := BitString.card_filter_eq_le_half_of_strictMajorityOn_ne
    (nonemptySubsets k) (vote predictor masks (fun j => x ⬝ᵥ masks j) i) (x i) herror
  have hcount := (Nat.mul_le_mul_left 2 hmajority).trans
    (show 2 * ((nonemptySubsets k).card / 2) ≤ (nonemptySubsets k).card by lia)
  have hreal := (Nat.cast_le (α := ℝ)).mpr hcount
  simpa only [Set.mem_ofPred_eq, X, score, ← vote_correct_iff, Finset.sum_boole,
    le_div_iff₀ (by norm_num : (0 : ℝ) < 2), Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hreal


private theorem failure_probability_le {n k : ℕ} (predictor : BitString n → Bool)
    (x : BitString n) (ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (h : 1 / 2 + ε ≤ agreement predictor x) :
    (PMF.uniformOfFintype (Fin k → BitString n)).toOuterMeasure
        {masks | x ∉ candidates predictor masks} ≤
      ENNReal.ofReal ((n : ℝ) / (4 * ε ^ 2 * (nonemptySubsets k).card)) := by
  let μ := (PMF.uniformOfFintype (Fin k → BitString n)).toMeasure
  have hsubset : {masks : Fin k → BitString n | x ∉ candidates predictor masks} ⊆
      ⋃ i, {masks | candidate predictor masks (fun j => x ⬝ᵥ masks j) i ≠ x i} := by
    intro masks hmiss
    apply Set.mem_iUnion.mpr
    by_contra hnone
    have heq : candidate predictor masks (fun j => x ⬝ᵥ masks j) = x := by
      funext i
      simpa using not_exists.mp hnone i
    exact hmiss (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, heq⟩)
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.to_countable _).measurableSet]
  change μ _ ≤ _
  calc
    _ ≤ μ (⋃ i, {masks | candidate predictor masks (fun j => x ⬝ᵥ masks j) i ≠ x i}) :=
      measure_mono hsubset
    _ ≤ ∑' i, μ {masks | candidate predictor masks (fun j => x ⬝ᵥ masks j) i ≠ x i} :=
      measure_iUnion_le _
    _ ≤ ∑ i : Fin n, ENNReal.ofReal
        (1 / (4 * ε ^ 2 * (nonemptySubsets k).card)) := by
      rw [tsum_fintype]
      exact Finset.sum_le_sum (fun i _ => coordinate_error_le predictor x i ε hε hk h)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1
      ring

/-- Sample the base masks uniformly and return all candidates. This is a distributional
specification; no machine-runtime certificate is asserted here. -/
noncomputable def decode {n : ℕ} (predictor : BitString n → Bool) (k : ℕ) :
    PMF (Finset (BitString n)) :=
  (PMF.uniformOfFintype (Fin k → BitString n)).map (candidates predictor)

/-- The decoder misses a parity correlated with its predictor with probability at most
`n / (4 * ε ^ 2 * (2 ^ k - 1))`. A union bound suffices across coordinates. -/
theorem decode_failure_le {n k : ℕ} (predictor : BitString n → Bool)
    (x : BitString n) (ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (h : 1 / 2 + ε ≤ agreement predictor x) :
    (decode predictor k).toOuterMeasure {list | x ∉ list} ≤
      ENNReal.ofReal ((n : ℝ) / (4 * ε ^ 2 * (2 ^ k - 1 : ℕ))) := by
  rw [decode, PMF.toOuterMeasure_map_apply]
  change (PMF.uniformOfFintype (Fin k → BitString n)).toOuterMeasure
    {masks | x ∉ candidates predictor masks} ≤ _
  simpa only [card_nonemptySubsets] using failure_probability_le predictor x ε hε hk h

/-- With sufficiently many subset masks, the candidate list contains the target with
probability at least one half. -/
theorem decode_failure_le_half {n k : ℕ} (predictor : BitString n → Bool)
    (x : BitString n) (ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (h : 1 / 2 + ε ≤ agreement predictor x)
    (hsize : (n : ℝ) ≤ 2 * ε ^ 2 * (2 ^ k - 1 : ℕ)) :
    (decode predictor k).toOuterMeasure {list | x ∉ list} ≤ 1 / 2 := by
  have hpow : 1 < 2 ^ k := Nat.one_lt_pow hk.ne' (by decide)
  have hcount : (0 : ℝ) < (2 ^ k - 1 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hpow
  calc
    _ ≤ ENNReal.ofReal ((n : ℝ) / (4 * ε ^ 2 * (2 ^ k - 1 : ℕ))) :=
      decode_failure_le predictor x ε hε hk h
    _ ≤ ENNReal.ofReal (1 / 2) := by
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    _ = _ := by simp

/-- For a perfect predictor, the true guessed parities recover the target for every choice
of base masks, including repeated or zero masks. -/
theorem candidate_parity {n k : ℕ} (x : BitString n)
    (masks : Fin k → BitString n) (hk : 0 < k) :
    candidate (fun r => x ⬝ᵥ r) masks (fun j => x ⬝ᵥ masks j) = x := by
  funext i
  have hv : vote (fun r => x ⬝ᵥ r) masks (fun j => x ⬝ᵥ masks j) i =
      fun _ => x i := by
    funext s
    exact (vote_correct_iff _ _ _ _ _).mpr rfl
  simp only [candidate, hv]
  exact BitString.strictMajorityOn_const _ ⟨{⟨0, hk⟩}, by simp⟩ _

/-- Every run against a perfect parity predictor includes that parity's defining string. -/
theorem mem_candidates_parity {n k : ℕ} (x : BitString n)
    (masks : Fin k → BitString n) (hk : 0 < k) :
    x ∈ candidates (fun r => x ⬝ᵥ r) masks :=
  Finset.mem_image.mpr ⟨_, Finset.mem_univ _, candidate_parity x masks hk⟩

/-- Agreement is exactly the success probability of predicting the Boolean inner product. -/
theorem agreement_eq_probability {n : ℕ} (predictor : BitString n → Bool) (x : BitString n) :
    agreement predictor x =
      ((PMF.uniformOfFintype (BitString n)).map
        (fun r => predictor r == x ⬝ᵥ r) true).toReal := by
  rw [agreement, PMF.integral_eq_sum]
  simp only [PMF.map, PMF.bind_apply_toReal, Function.comp_def, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : predictor r = x ⬝ᵥ r <;> simp [score, h, PMF.pure_apply]

/-- Agreement with any fixed parity is a probability, hence at most one. -/
theorem agreement_le_one {n : ℕ} (predictor : BitString n → Bool) (x : BitString n) :
    agreement predictor x ≤ 1 := by
  rw [agreement_eq_probability]
  exact PMF.toReal_apply_le_one _ _

/-- Every possible output of the decoder has at most `2 ^ k` candidates. -/
theorem card_le_of_mem_support_decode {n k : ℕ} (predictor : BitString n → Bool)
    {list : Finset (BitString n)} (h : list ∈ (decode predictor k).support) :
    list.card ≤ 2 ^ k := by
  obtain ⟨masks, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  exact card_candidates_le predictor masks

end Cslib.Crypto.GoldreichLevin
