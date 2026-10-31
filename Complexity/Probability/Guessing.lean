/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.UniversalHash
import Mathlib.Data.Finset.Max

import Complexity.Probability.PMF.Expect

/-!
# Guessing the remainder of a partially uniform string

If the prefix of a public string is close to uniform, replacing the whole string by a uniform
guess costs the size of the suffix space, together with the prefix's statistical error. The score
may be any number in `[0, 1]`, including a decoder's probability of returning a valid preimage.

## Main results

* `Cslib.Probability.score_le_uniform_guess`: replacing a partially uniform string by a guess.
* `Cslib.Probability.IsTwoUniversal.score_le_uniform_guess`: a universal hash supplies the error.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 4, Lemma 4, Games 2--5.
  We apply the guessing argument directly to a nonnegative success score, so no separate
  maximization of signed prediction advantage over preimages is needed.

Adapted from Probability/Guessing.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the pinned finite-PMF distance.
-/

@[expose] public section

namespace Cslib.Probability

open Cslib.Probability.PMF

variable {Seed Prefix Suffix : Type*} [Fintype Seed] [Fintype Prefix] [Fintype Suffix]
  [Nonempty Prefix] [Nonempty Suffix]

/-- A uniform suffix guess loses at most its cardinality. The prefix need only be statistically
close to uniform given the public seed; the full original string may depend on that seed. -/
theorem score_le_uniform_guess (real : PMF (Seed × (Prefix × Suffix))) (seed : PMF Seed)
    (score : Seed → Prefix × Suffix → ℝ)
    (hscore : ∀ s z, 0 ≤ score s z ∧ score s z ≤ 1) :
    (∑ pair, (real pair).toReal * score pair.1 pair.2) ≤
      2 * dist (real.map (fun pair => (pair.1, Prod.fst pair.2)))
        (seed.bind (fun s => (PMF.uniformOfFintype Prefix).map (s, ·))) +
      Fintype.card Suffix *
        ∑ s, (seed s).toReal * ∑ z,
          (PMF.uniformOfFintype (Prefix × Suffix) z).toReal * score s z := by
  classical
  let complete (s : Seed) (initial : Prefix) : Suffix :=
    Classical.choose (Finset.exists_max_image Finset.univ
      (fun suffix => score s (initial, suffix)) Finset.univ_nonempty)
  let best (pair : Seed × Prefix) := score pair.1 (pair.2, complete pair.1 pair.2)
  have hbest (s : Seed) (initial : Prefix) (suffix : Suffix) :
      score s (initial, suffix) ≤ best (s, initial) :=
    (Classical.choose_spec (Finset.exists_max_image Finset.univ
      (fun suffix => score s (initial, suffix)) Finset.univ_nonempty)).2 suffix (Finset.mem_univ _)
  let ideal := seed.bind (fun s => (PMF.uniformOfFintype Prefix).map (s, ·))
  have hchange := abs_sum_mul_sub_le
    (real.map (fun pair => (pair.1, pair.2.1))) ideal best
    (bound := 1) (fun pair => by
      rw [abs_of_nonneg (hscore _ _).1]
      exact (hscore _ _).2)
  have hguess (s : Seed) :
      (∑ initial, (PMF.uniformOfFintype Prefix initial).toReal * best (s, initial)) ≤
        Fintype.card Suffix * ∑ z,
          (PMF.uniformOfFintype (Prefix × Suffix) z).toReal * score s z := by
    have hcard : (Fintype.card Suffix : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    calc
      _ ≤ ∑ initial, (PMF.uniformOfFintype Prefix initial).toReal *
          ∑ suffix, score s (initial, suffix) := by
        apply Finset.sum_le_sum
        intro initial _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        exact Finset.single_le_sum (fun suffix _ => (hscore _ _).1)
          (Finset.mem_univ (complete s initial))
      _ = _ := by
        simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          Fintype.card_prod, Nat.cast_mul, ENNReal.toReal_mul, mul_inv, Fintype.sum_prod_type,
          Finset.mul_sum, ← mul_assoc]
        field_simp
  calc
    _ ≤ ∑ pair, (real pair).toReal * best (pair.1, pair.2.1) :=
      Finset.sum_le_sum (fun pair _ =>
        mul_le_mul_of_nonneg_left (hbest _ _ _) ENNReal.toReal_nonneg)
    _ = ∑ pair, ((real.map (fun pair => (pair.1, pair.2.1))) pair).toReal * best pair :=
      (sum_map_mul _ _ _).symm
    _ ≤ (∑ pair, (ideal pair).toReal * best pair) + 2 * dist _ ideal := by
      have h := (le_abs_self _).trans hchange
      linarith
    _ ≤ _ := by
      simp only [ideal, sum_bind_mul, sum_map_mul]
      rw [add_comm, Finset.mul_sum]
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro s _
      simpa only [mul_left_comm] using
        mul_le_mul_of_nonneg_left (hguess s) (ENNReal.toReal_nonneg (a := seed s))

/-- If a hash prefix is two-universal, the leftover hash lemma bounds the cost of replacing
the complete digest by a uniform guess. The suffix itself need not be a universal hash. -/
theorem IsTwoUniversal.score_le_uniform_guess {Input : Type*} [Fintype Input]
    {seed : PMF Seed} {hash : Seed → Input → Prefix × Suffix}
    (hhash : IsTwoUniversal seed (fun s x => (hash s x).1)) (source : PMF Input)
    (score : Seed → Prefix × Suffix → ℝ)
    (hscore : ∀ s z, 0 ≤ score s z ∧ score s z ≤ 1) :
    (∑ s, (seed s).toReal * ∑ x, (source x).toReal * score s (hash s x)) ≤
      Real.sqrt (Fintype.card Prefix * collisionProbability source) +
      Fintype.card Suffix * ∑ s, (seed s).toReal * ∑ z,
        (PMF.uniformOfFintype (Prefix × Suffix) z).toReal * score s z := by
  have h := Cslib.Probability.score_le_uniform_guess (seededHash seed source hash) seed score hscore
  simp only [seededHash, sum_bind_mul, sum_map_mul, PMF.map_bind, PMF.map_comp,
    Function.comp_def] at h
  apply h.trans
  apply add_le_add _ le_rfl
  have hdist := hhash.leftover_hash source
  dsimp only [seededHash] at hdist
  linarith

end Cslib.Probability
