/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.AndreevLowerBound
import Complexity.Foundations.Combinatorics.ApproximateMajority

/-!
# Approximate majorities of depth-two threshold circuits for Andreev's function

Let `C : Fin t → Circuit signature n 1`, `n = 2 ^ b + b * m`, be depth-two weighted threshold
circuits. The family is an *`ε`-approximate majority* for Andreev's function when on every input
at least `t (1 / 2 + ε)` members output `andreev b m`. Averaging
(`Cslib.exists_mul_card_le_card_filter_of_forall`) gives one member agreeing with Andreev's
function on a `1 / 2 + ε` fraction of inputs, so the average-case bounds of `AndreevLowerBound`
apply with any common bound `s` on the members' gate counts or active wire counts.

A majority vote over the family computes Andreev's function when on every input *strictly* more
than `t / 2` members are correct. The family is then a `1 / (2 t)`-approximate majority, and when
`3 (b + 2) / √(2 ^ b) ≤ 1 / (2 t)` the bounds read
`m · 2^b ≤ 576 (b + 2) · t² · s · √n` for gates and `m · √m · 2^b ≤ 576 (b + 2) · t² · s` for
active wires (`m ≤ 2 ^ b`). In the balanced regime `2 ^ b = b m` this is the top fan-in bound
`t = Ω(n^(3/4) / (log n · √s))` for unweighted-majority-of-`THR ∘ THR` circuits with at most `s`
gates in each subcircuit, as long as `t ≤ √(2 ^ b) / (6 (b + 2))`; a larger `t` already exceeds
`Ω(√n / log n)`.

The vote is modelled by its correctness count rather than by a depth-three circuit: the hypothesis
is `t < 2 * #{i | (C i).eval interpretation w 0 = andreev b m w}` for every input `w`. For odd `t`
this is exactly the statement that the strict-majority vote of the outputs computes Andreev's
function (`Cslib.lt_two_mul_card_filter_eq_of_strictMajority_eq`); the subcircuits need not share
gates, and the top gate is not counted in `s`.

These follow [KaneWilliams2016], `arXiv:1511.07860v1`, Corollary 1.1 and Section 5.2, with the
improved `ε²` dependence of `AndreevLowerBound` in place of their `ε³`. That improvement, and hence
the `n^(3/4) / √s` top fan-in bound in place of their `n^(1/2) / s^(1/3)`, are original; they are
not claims attributed to that paper. All results are explicit finite inequalities.

## Main results

* `exists_card_eval_eq_andreev_ge_of_approxMajority`: averaging an approximate majority.
* `size_ge_of_approxMajority_andreev`, `size_ge_of_approxMajority_andreev_of_le_two_pow`,
  `wireCount_ge_of_approxMajority_andreev`, `wireCount_ge_of_approxMajority_andreev_of_le_two_pow`:
  gate and wire bounds for approximate majorities.
* `size_ge_of_majorityVote_andreev`, `size_ge_of_majorityVote_andreev_of_le_two_pow`,
  `wireCount_ge_of_majorityVote_andreev`, `wireCount_ge_of_majorityVote_andreev_of_le_two_pow`:
  top fan-in bounds for majority votes.

## References

* [D. M. Kane and R. Williams, *Super-Linear Gate and Super-Quadratic Wire Lower Bounds for
  Depth-Two and Depth-Three Threshold Circuits*][KaneWilliams2016]
-/

public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset

/-! ### Averaging an approximate majority -/

/-- **Averaging.** If on every input at least `t (1 / 2 + ε)` of the circuits `C i` output Andreev's
function, then one of them agrees with it on at least a `1 / 2 + ε` fraction of all inputs. -/
theorem exists_card_eval_eq_andreev_ge_of_approxMajority {b m t : ℕ} (ht : 0 < t) {ε : ℝ}
    (C : Fin t → Circuit signature (2 ^ b + b * m) 1)
    (hmaj : ∀ w : BitString (2 ^ b + b * m),
      (t : ℝ) * (1 / 2 + ε) ≤ (#{i | (C i).eval interpretation w 0 = andreev b m w} : ℝ)) :
    ∃ i, (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      (#{w : BitString (2 ^ b + b * m) | (C i).eval interpretation w 0 = andreev b m w} : ℝ) := by
  have : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
  obtain ⟨i, hi⟩ := exists_mul_card_le_card_filter_of_forall
    (fun i w => (C i).eval interpretation w 0 = andreev b m w) (r := 1 / 2 + ε)
    fun w => by simpa only [Fintype.card_fin, mul_comm] using hmaj w
  refine ⟨i, ?_⟩
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat, mul_comm] using hi

/-- An agreement fraction `1 / 2 + ε` forces `ε ≤ 1 / 2`. -/
private theorem le_half_of_card_eval_eq_andreev_ge {b m : ℕ} {ε : ℝ}
    (c : Circuit signature (2 ^ b + b * m) 1)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w 0 = andreev b m w} : ℝ)) :
    ε ≤ 1 / 2 := by
  have hle : (#{w : BitString (2 ^ b + b * m) | c.eval interpretation w 0 = andreev b m w} : ℝ) ≤
      (2 : ℝ) ^ (2 ^ b + b * m) := by
    have h := card_filter_le (univ : Finset (BitString (2 ^ b + b * m)))
      fun w => c.eval interpretation w 0 = andreev b m w
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at h
    exact_mod_cast h
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ b + b * m) := by positivity
  nlinarith

/-! ### Gate and wire bounds for approximate majorities -/

/-- Gate bound for an `ε`-approximate majority of depth-two circuits with at most `s` gates each. -/
theorem size_ge_of_approxMajority_andreev {b m t : ℕ} (hm : 0 < m) (ht : 0 < t) {ε : ℝ}
    (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (C : Fin t → Circuit signature (2 ^ b + b * m) 1) (hd : ∀ i, (C i).depth ≤ 2)
    {s : ℕ} (hs : ∀ i, (C i).size ≤ s)
    (hmaj : ∀ w : BitString (2 ^ b + b * m),
      (t : ℝ) * (1 / 2 + ε) ≤ (#{i | (C i).eval interpretation w 0 = andreev b m w} : ℝ)) :
    (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      36 * ((b : ℝ) + 2 + Real.log (s + 1)) * (s : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
  obtain ⟨i, hi⟩ := exists_card_eval_eq_andreev_ge_of_approxMajority ht C hmaj
  have hsi : ((C i).size : ℝ) ≤ s := by exact_mod_cast hs i
  have hlog : 0 ≤ Real.log ((s : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
  refine (size_ge_of_card_eval_eq_andreev_ge_of_le_eps hm hε (C i) (hd i) 0 hi).trans ?_
  gcongr

/-- Gate bound for an `ε`-approximate majority of depth-two circuits with at most `s` gates each,
with a linear counting loss in `b`, valid when `m ≤ 2 ^ b`. -/
theorem size_ge_of_approxMajority_andreev_of_le_two_pow {b m t : ℕ} (hm : 0 < m)
    (hmN : m ≤ 2 ^ b) (ht : 0 < t) {ε : ℝ}
    (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (C : Fin t → Circuit signature (2 ^ b + b * m) 1) (hd : ∀ i, (C i).depth ≤ 2)
    {s : ℕ} (hs : ∀ i, (C i).size ≤ s)
    (hmaj : ∀ w : BitString (2 ^ b + b * m),
      (t : ℝ) * (1 / 2 + ε) ≤ (#{i | (C i).eval interpretation w 0 = andreev b m w} : ℝ)) :
    (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      144 * ((b : ℝ) + 2) * (s : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
  obtain ⟨i, hi⟩ := exists_card_eval_eq_andreev_ge_of_approxMajority ht C hmaj
  have hε1 : ε ≤ 1 := (le_half_of_card_eval_eq_andreev_ge (C i) hi).trans (by norm_num)
  have hsi : ((C i).size : ℝ) ≤ s := by exact_mod_cast hs i
  refine (size_ge_of_card_eval_eq_andreev_ge_of_le_two_pow hm hmN hε hε1 (C i) (hd i) 0
    hi).trans ?_
  gcongr

/-- Wire bound for an `ε`-approximate majority of depth-two circuits with at most `s` active wires
each. -/
theorem wireCount_ge_of_approxMajority_andreev {b m t : ℕ} (hm : 0 < m) (ht : 0 < t) {ε : ℝ}
    (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (C : Fin t → Circuit signature (2 ^ b + b * m) 1) (hd : ∀ i, (C i).depth ≤ 2)
    {s : ℕ} (hs : ∀ i, (C i).wireCount ≤ s)
    (hmaj : ∀ w : BitString (2 ^ b + b * m),
      (t : ℝ) * (1 / 2 + ε) ≤ (#{i | (C i).eval interpretation w 0 = andreev b m w} : ℝ)) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      36 * ((b : ℝ) + 2 + Real.log (s + 1)) * (s : ℝ) := by
  obtain ⟨i, hi⟩ := exists_card_eval_eq_andreev_ge_of_approxMajority ht C hmaj
  have hsi : ((C i).wireCount : ℝ) ≤ s := by exact_mod_cast hs i
  have hlog : 0 ≤ Real.log ((s : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
  refine (wireCount_ge_of_card_eval_eq_andreev_ge_of_le_eps hm hε (C i) (hd i) 0 hi).trans ?_
  gcongr

/-- Wire bound for an `ε`-approximate majority of depth-two circuits with at most `s` active wires
each, with a linear counting loss in `b`, valid when `m ≤ 2 ^ b`. -/
theorem wireCount_ge_of_approxMajority_andreev_of_le_two_pow {b m t : ℕ} (hm : 0 < m)
    (hmN : m ≤ 2 ^ b) (ht : 0 < t) {ε : ℝ}
    (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (C : Fin t → Circuit signature (2 ^ b + b * m) 1) (hd : ∀ i, (C i).depth ≤ 2)
    {s : ℕ} (hs : ∀ i, (C i).wireCount ≤ s)
    (hmaj : ∀ w : BitString (2 ^ b + b * m),
      (t : ℝ) * (1 / 2 + ε) ≤ (#{i | (C i).eval interpretation w 0 = andreev b m w} : ℝ)) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤ 144 * ((b : ℝ) + 2) * (s : ℝ) := by
  obtain ⟨i, hi⟩ := exists_card_eval_eq_andreev_ge_of_approxMajority ht C hmaj
  have hε1 : ε ≤ 1 := (le_half_of_card_eval_eq_andreev_ge (C i) hi).trans (by norm_num)
  have hsi : ((C i).wireCount : ℝ) ≤ s := by exact_mod_cast hs i
  refine (wireCount_ge_of_card_eval_eq_andreev_ge_of_le_two_pow hm hmN hε hε1 (C i) (hd i) 0
    hi).trans ?_
  gcongr

/-! ### Top fan-in of majority votes -/

/-- A strict majority of `t` votes is a `1 / (2 t)`-approximate majority. -/
private theorem mul_half_add_inv_le_of_lt_two_mul {t k : ℕ} (h : t < 2 * k) :
    (t : ℝ) * (1 / 2 + 1 / (2 * t)) ≤ k := by
  have h' : (t : ℝ) + 1 ≤ 2 * k := by exact_mod_cast h
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · have htinv : (t : ℝ) * (1 / (2 * t)) = 1 / 2 := by field_simp
    rw [mul_add, htinv]
    linarith

/-- On every input strictly more than half of the votes are correct, so the family is nonempty. -/
private theorem pos_of_majorityVote {b m t : ℕ} (C : Fin t → Circuit signature (2 ^ b + b * m) 1)
    (hvote : ∀ w : BitString (2 ^ b + b * m),
      t < 2 * #{i | (C i).eval interpretation w 0 = andreev b m w}) : 0 < t := by
  have h := hvote fun _ => false
  have hle := card_filter_le (univ : Finset (Fin t))
    fun i => (C i).eval interpretation (fun _ => false) 0 = andreev b m fun _ => false
  rw [card_univ, Fintype.card_fin] at hle
  omega

/-- Multiplying the `ε = 1 / (2 t)` bound by `4 t²`. -/
private theorem le_four_mul_sq_mul_of_mul_inv_sq_le {t : ℕ} (ht : 0 < t) {L R : ℝ}
    (h : L * (1 / (2 * (t : ℝ))) ^ 2 ≤ R) : L ≤ 4 * (t : ℝ) ^ 2 * R := by
  have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have hL : L = 4 * (t : ℝ) ^ 2 * (L * (1 / (2 * (t : ℝ))) ^ 2) := by
    field_simp; ring
  rw [hL]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **Top fan-in, gates.** If on every input strictly more than half of the depth-two circuits
`C i` (each with at most `s` gates) output Andreev's function, and
`3 (b + 2) / √(2 ^ b) ≤ 1 / (2 t)`, then `m · 2^b ≤ 144 t² (b + 2 + log (s + 1)) s √n`. -/
theorem size_ge_of_majorityVote_andreev {b m t : ℕ} (hm : 0 < m)
    (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / (2 * t))
    (C : Fin t → Circuit signature (2 ^ b + b * m) 1) (hd : ∀ i, (C i).depth ≤ 2)
    {s : ℕ} (hs : ∀ i, (C i).size ≤ s)
    (hvote : ∀ w : BitString (2 ^ b + b * m),
      t < 2 * #{i | (C i).eval interpretation w 0 = andreev b m w}) :
    (m : ℝ) * (2 : ℝ) ^ b ≤
      144 * (t : ℝ) ^ 2 * ((b : ℝ) + 2 + Real.log (s + 1)) * (s : ℝ) *
        Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
  have ht := pos_of_majorityVote C hvote
  have h := le_four_mul_sq_mul_of_mul_inv_sq_le ht (size_ge_of_approxMajority_andreev hm ht hb C hd
    hs fun w => mul_half_add_inv_le_of_lt_two_mul (hvote w))
  linarith

/-- **Top fan-in, gates**, with a linear counting loss in `b`, valid when `m ≤ 2 ^ b`: a majority
vote as in `size_ge_of_majorityVote_andreev` has `m · 2^b ≤ 576 (b + 2) t² s √n`. -/
theorem size_ge_of_majorityVote_andreev_of_le_two_pow {b m t : ℕ} (hm : 0 < m)
    (hmN : m ≤ 2 ^ b) (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / (2 * t))
    (C : Fin t → Circuit signature (2 ^ b + b * m) 1) (hd : ∀ i, (C i).depth ≤ 2)
    {s : ℕ} (hs : ∀ i, (C i).size ≤ s)
    (hvote : ∀ w : BitString (2 ^ b + b * m),
      t < 2 * #{i | (C i).eval interpretation w 0 = andreev b m w}) :
    (m : ℝ) * (2 : ℝ) ^ b ≤
      576 * ((b : ℝ) + 2) * (t : ℝ) ^ 2 * (s : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
  have ht := pos_of_majorityVote C hvote
  have h := le_four_mul_sq_mul_of_mul_inv_sq_le ht (size_ge_of_approxMajority_andreev_of_le_two_pow
    hm hmN ht hb C hd hs fun w => mul_half_add_inv_le_of_lt_two_mul (hvote w))
  linarith

/-- **Top fan-in, wires.** If on every input strictly more than half of the depth-two circuits
`C i` (each with at most `s` active wires) output Andreev's function, and
`3 (b + 2) / √(2 ^ b) ≤ 1 / (2 t)`, then `m · √m · 2^b ≤ 144 t² (b + 2 + log (s + 1)) s`. -/
theorem wireCount_ge_of_majorityVote_andreev {b m t : ℕ} (hm : 0 < m)
    (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / (2 * t))
    (C : Fin t → Circuit signature (2 ^ b + b * m) 1) (hd : ∀ i, (C i).depth ≤ 2)
    {s : ℕ} (hs : ∀ i, (C i).wireCount ≤ s)
    (hvote : ∀ w : BitString (2 ^ b + b * m),
      t < 2 * #{i | (C i).eval interpretation w 0 = andreev b m w}) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b ≤
      144 * (t : ℝ) ^ 2 * ((b : ℝ) + 2 + Real.log (s + 1)) * (s : ℝ) := by
  have ht := pos_of_majorityVote C hvote
  have h := le_four_mul_sq_mul_of_mul_inv_sq_le ht (wireCount_ge_of_approxMajority_andreev hm ht hb
    C hd hs fun w => mul_half_add_inv_le_of_lt_two_mul (hvote w))
  linarith

/-- **Top fan-in, wires**, with a linear counting loss in `b`, valid when `m ≤ 2 ^ b`: a majority
vote as in `wireCount_ge_of_majorityVote_andreev` has `m · √m · 2^b ≤ 576 (b + 2) t² s`. -/
theorem wireCount_ge_of_majorityVote_andreev_of_le_two_pow {b m t : ℕ} (hm : 0 < m)
    (hmN : m ≤ 2 ^ b) (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / (2 * t))
    (C : Fin t → Circuit signature (2 ^ b + b * m) 1) (hd : ∀ i, (C i).depth ≤ 2)
    {s : ℕ} (hs : ∀ i, (C i).wireCount ≤ s)
    (hvote : ∀ w : BitString (2 ^ b + b * m),
      t < 2 * #{i | (C i).eval interpretation w 0 = andreev b m w}) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b ≤
      576 * ((b : ℝ) + 2) * (t : ℝ) ^ 2 * (s : ℝ) := by
  have ht := pos_of_majorityVote C hvote
  have h := le_four_mul_sq_mul_of_mul_inv_sq_le ht
    (wireCount_ge_of_approxMajority_andreev_of_le_two_pow hm hmN ht hb C hd hs
      fun w => mul_half_add_inv_le_of_lt_two_mul (hvote w))
  linarith

end Cslib.Circuits.Boolean.WeightedThreshold
