/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.PMF.Event
import Complexity.Probability.BitString.LinearHash
import Complexity.Probability.BoundedDifferences
import Complexity.Probability.Concentration
import Complexity.Probability.MinEntropy.Flat
import Complexity.Probability.MinEntropy.LeftoverHash

/-! Min-entropy, `(k, ε)`-sources, flat decompositions, leftover hashing from sources and
McDiarmid's inequality: concrete instances and satisfiable hypotheses. -/

namespace ComplexityTests.ProbabilityToolkit3

open Cslib Cslib.Probability Cslib.Probability.PMF Finset
open scoped NNReal Cslib.Probability.PMF

/-! ### Min-entropy of concrete distributions -/

-- A fair coin has one bit of min-entropy, and a point mass has none.
example : minEntropy (uniformOfFintype Bool) = 1 := by simp

example : minEntropy (PMF.pure true) = 0 := minEntropy_pure true

/-- A source on three outcomes with masses `1/2, 1/4, 1/4`; it is not flat. -/
private noncomputable def lopsided : PMF (Fin 3) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (![1 / 2, 1 / 4, 1 / 4] i)) (by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

private theorem lopsided_apply (i : Fin 3) :
    (lopsided i).toReal = ![1 / 2, 1 / 4, 1 / 4] i := by
  rw [lopsided, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  fin_cases i <;> norm_num

/-- No outcome of `lopsided` has probability above `1/2`, so it is a `1`-source. -/
private theorem one_le_minEntropy_lopsided : (1 : ℝ) ≤ minEntropy lopsided := by
  rw [le_minEntropy_iff]
  intro i
  rw [lopsided_apply, Real.rpow_neg_one]
  fin_cases i <;> norm_num

-- Its min-entropy is exactly one bit, attained at the heavy outcome.
example : minEntropy lopsided = 1 := by
  have hmass := lopsided_apply 0
  simp only [Matrix.cons_val_zero] at hmass
  have hsupport : (0 : Fin 3) ∈ lopsided.support := by
    rw [PMF.mem_support_iff]
    intro h
    rw [h, ENNReal.toReal_zero] at hmass
    norm_num at hmass
  refine le_antisymm ((minEntropy_le_surprisal lopsided hsupport).trans_eq ?_)
    one_le_minEntropy_lopsided
  rw [surprisal, hmass, one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num), neg_neg]

/-! ### Flat decompositions -/

-- The non-flat `1`-source `lopsided` is a mixture of flat distributions on pairs of outcomes.
example : ∃ mix : PMF {S : Finset (Fin 3) // S.card = 2 ^ 1},
    lopsided = mix.bind fun S =>
      uniformOfFinset S.1 (card_ne_zero.mp (S.2.trans_ne (pow_ne_zero 1 two_ne_zero))) :=
  exists_eq_bind_uniformOfFinset_of_le_minEntropy lopsided (by
    simpa only [Nat.cast_one] using one_le_minEntropy_lopsided)

-- Conversely, every mixture of flat distributions on pairs is a `1`-source; in particular, a
-- point-mass mixture on `{0, 1}` gives `1 ≤ minEntropy (uniformOfFinset {0, 1} _)`.
example : 1 ≤ minEntropy (uniformOfFinset ({0, 1} : Finset (Fin 3)) (by decide)) := by
  let S0 : {S : Finset (Fin 3) // S.card = 2 ^ 1} := ⟨{0, 1}, by decide⟩
  have h := (le_minEntropy_iff_exists_eq_bind_uniformOfFinset
    (uniformOfFinset ({0, 1} : Finset (Fin 3)) (by decide)) 1).mpr ⟨PMF.pure S0, by simp [S0]⟩
  simpa using h

-- The uniform distribution on `{0, 1} ⊆ Fin 3` assigns measure `1 / 2` to `{0, 2}`.
example :
    (uniformOfFinset ({0, 1} : Finset (Fin 3)) (by decide)).toMeasure ({0, 2} : Set (Fin 3)) =
      1 / 2 := by
  rw [toMeasure_uniformOfFinset ({0, 1} : Finset (Fin 3)) (by decide) trivial]
  have h1 : (({0, 1} : Finset (Fin 3)).filter (· ∈ ({0, 2} : Set (Fin 3)))).card = 1 := by decide
  have h2 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  rw [h1, h2]
  norm_num

/-! ### Weak random sources -/

/-- Uniform bit strings are sources of their full length. -/
private theorem isSource_uniform (n : ℕ) : IsSource (uniformOfFintype (BitString n)) n 0 := by
  rw [isSource_zero_iff, minEntropy_uniformOfFintype, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one one_lt_two, mul_one]

/-- `2⁻²` is a quarter. -/
private theorem two_rpow_neg_two : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_two]
  norm_num

-- Discarding the heavy outcome, of probability `1/2`, makes `lopsided` a `(1, 1/2)`-source.
example : IsSource lopsided 1 (1 / 2) := by
  have hheavy : (lopsided.toOuterMeasure
      {a | 2 ^ (-(2 : ℝ)) < (lopsided a).toReal}).toReal ≤ ((1 / 2 : ℝ≥0) : ℝ) := by
    rw [toOuterMeasure_apply_toReal, Fin.sum_univ_three]
    simp only [Set.mem_ofPred_eq, lopsided_apply, two_rpow_neg_two]
    norm_num
  have h := isSource_of_heavy_le lopsided (by norm_num) hheavy
  have hk : (2 : ℝ) + Real.logb 2 (1 - ((1 / 2 : ℝ≥0) : ℝ)) = 1 := by
    rw [show (1 : ℝ) - ((1 / 2 : ℝ≥0) : ℝ) = 2⁻¹ by norm_num, Real.logb_inv,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rwa [hk] at h

/-! ### Leftover hashing from sources -/

-- Random Boolean matrices extract from every `(k, ε)`-source on bit strings: on a `(6, 0)`-source
-- hashed to `2` bits, `leftover_hash_of_isSource` bounds the statistical distance by `1 / 8`.
example :
    dist (seededHash (uniformOfFintype (BitString (2 * 6))) (uniformOfFintype (BitString 6))
        fun seed => BitString.LinearHash.hash (BitString.blocksEquiv seed))
      ((uniformOfFintype (BitString (2 * 6))).bind
        fun s => (uniformOfFintype (BitString 2)).map (s, ·)) ≤ 1 / 8 := by
  have hsource : IsSource (uniformOfFintype (BitString 6)) 6 0 := by
    simpa using isSource_uniform 6
  have h := (BitString.LinearHash.isTwoUniversal_flat 6 2).leftover_hash_of_isSource hsource
  refine h.trans_eq ?_
  simp only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, NNReal.coe_zero,
    zero_add]
  rw [Real.rpow_neg (by norm_num),
    show ((2 ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (6 : ℝ))⁻¹ = (1 / 4) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

-- Hashing a uniform `8`-bit source to `4` bits loses `2 log₂ 4 = 4` bits and errs by `1/8`.
example :
    dist (seededHash (uniformOfFintype (BitString (4 * 8))) (uniformOfFintype (BitString 8))
        fun seed => BitString.LinearHash.hash (BitString.blocksEquiv seed))
      ((uniformOfFintype (BitString (4 * 8))).bind
        fun s => (uniformOfFintype (BitString 4)).map (s, ·)) ≤ 0 + (1 / 4) / 2 := by
  refine (BitString.LinearHash.isTwoUniversal_flat 8 4).leftover_hash_of_isSource_of_logb_le
    ((isSource_zero_iff _).mpr le_rfl) (by norm_num) ?_
  rw [minEntropy_uniformOfFintype]
  simp only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat, inv_div, div_one]
  rw [Real.logb_pow, Real.logb_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  norm_num

/-! ### McDiarmid's inequality -/

/-- The number of heads among `n` coins: Hoeffding's setting. -/
private def heads (n : ℕ) (x : Fin n → Bool) : ℝ := ∑ i, if x i then 1 else 0

private theorem hasBoundedDifferences_heads (n : ℕ) :
    HasBoundedDifferences (heads n) fun _ => 1 :=
  hasBoundedDifferences_sum (score := fun _ (b : Bool) => if b then (1 : ℝ) else 0) fun _ a b => by
    cases a <;> cases b <;> norm_num

/-- The number of distinct values among `n` samples, which is not a sum of coordinate scores. -/
private def distinct {γ : Type*} [DecidableEq γ] (n : ℕ) (x : Fin n → γ) : ℝ :=
  (univ.image x).card

/-- Samples that agree off coordinate `i` have at most one more distinct value than each other. -/
private theorem card_image_le_of_agree {γ : Type*} [DecidableEq γ] {n : ℕ} {y z : Fin n → γ}
    {i : Fin n} (h : ∀ j, j ≠ i → y j = z j) : (univ.image y).card ≤ (univ.image z).card + 1 := by
  refine (card_le_card fun c hc => ?_).trans (card_insert_le (y i) _)
  obtain ⟨j, -, rfl⟩ := mem_image.mp hc
  by_cases hj : j = i
  · subst hj
    exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_image.mpr ⟨j, mem_univ j, (h j hj).symm⟩)

/-- Changing one sample changes the number of distinct values by at most one. -/
private theorem hasBoundedDifferences_distinct {γ : Type*} [DecidableEq γ] (n : ℕ) :
    HasBoundedDifferences (distinct (γ := γ) n) fun _ => 1 := by
  intro x i a
  have hagree (j : Fin n) (hj : j ≠ i) : Function.update x i a j = x j :=
    Function.update_of_ne hj a x
  have h₁ : ((univ.image (Function.update x i a)).card : ℝ) ≤ (univ.image x).card + 1 := by
    exact_mod_cast card_image_le_of_agree hagree
  have h₂ : ((univ.image x).card : ℝ) ≤ (univ.image (Function.update x i a)).card + 1 := by
    exact_mod_cast card_image_le_of_agree fun j hj => (hagree j hj).symm
  change |((univ.image (Function.update x i a)).card : ℝ) - (univ.image x).card| ≤ 1
  rw [abs_sub_le_iff]
  constructor <;> linarith

-- By linearity of expectation under `pi`, `n` fair coins have mean `n / 2` heads.
example (n : ℕ) :
    ∑ y, ((pi fun _ : Fin n => uniformOfFintype Bool) y).toReal * heads n y = n / 2 := by
  refine (sum_pi_mul_sum (fun _ : Fin n => uniformOfFintype Bool)
    (fun _ b => if b then (1 : ℝ) else 0)).trans ?_
  simp [div_eq_mul_inv]

-- A fair-coin instance: the number of heads exceeds its mean by `ε` with probability at most
-- `exp (-2 ε² / n)`.
example (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ((pi fun _ : Fin n => uniformOfFintype Bool).toOuterMeasure
      {x | (∑ y, ((pi fun _ : Fin n => uniformOfFintype Bool) y).toReal * heads n y) + ε ≤
        heads n x}).toReal ≤ Real.exp (-2 * ε ^ 2 / n) := by
  have h := (hasBoundedDifferences_heads n).pi_ge_mean_add (fun _ => uniformOfFintype Bool) hε
  rwa [Finset.sum_const, one_pow, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h

-- The number of distinct values among `n` independent samples concentrates in both directions.
example {γ : Type*} [Fintype γ] [DecidableEq γ] (n : ℕ) (p : PMF γ) {ε : ℝ} (hε : 0 ≤ ε) :
    ((pi fun _ : Fin n => p).toOuterMeasure
      {x | ε ≤ |distinct n x - ∑ y, ((pi fun _ : Fin n => p) y).toReal * distinct n y|}).toReal ≤
        2 * Real.exp (-2 * ε ^ 2 / n) := by
  have h := (hasBoundedDifferences_distinct n).pi_abs_sub_mean_ge (fun _ => p) hε
  rwa [Finset.sum_const, one_pow, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h

end ComplexityTests.ProbabilityToolkit3
