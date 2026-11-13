/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.NearestDecoding
public import CslibFrontier.Foundations.BooleanAnalysis.Bernoulli
public import CslibFrontier.Probability.Product
public import CslibFrontier.Probability.PMF.Coin
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Topology.UnitInterval
import CslibFrontier.Foundations.Combinatorics.BinomialTail
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The binary symmetric channel

The binary symmetric channel `BSC_p` with crossover probability `p ∈ [0, 1]` flips every bit of
its input independently with probability `p` [Guruswami, Rudra and Sudan, Section 6.2]
[GuruswamiRudraSudan2019]; it is the symmetric channel on two symbols of
[Shannon, Section 16][Shannon1948], of capacity `1 - h₂(p)` bits per use. Here it is the probability
mass function `Cslib.BitString.bsc p x` on received words `y : ι → Bool`, the translate by `x` of
the noise `Cslib.BitString.bscNoise p`, an independent product (`Cslib.Probability.PMF.pi`) of
coins `Cslib.Probability.PMF.coin p` showing `true` with probability `p`. It delivers `y` with
probability `p ^ d (1 - p) ^ (n - d)`, where `d` is the Hamming distance of `x` and `y`
(`Cslib.BitString.bsc_apply_toReal`); the noise has the law of a random mask of rate `p`
(`Cslib.BitString.bscNoise_apply_toReal`), so its weight is binomially distributed and exceeds
`r ≥ n p - 1` with probability at most `exp (-2 (r + 1 - n p) ^ 2 / n)` by Hoeffding's
inequality (`Cslib.BitString.bscNoise_toOuterMeasure_lt_weight_toReal_le`).

A code with message set `M` is an encoder `E : M → (ι → Bool)` with a decoder
`D : (ι → Bool) → M`, and `Cslib.BitString.decodingError p E D m` is the probability that `D`
fails to recover `m` from the channel output on `E m`. A decoder is a nearest-codeword decoder
(`Cslib.BitString.IsNearestDecoder`) if it always returns a message whose codeword is closest to
the received word; such decoders exist for every finite nonempty message set, and for `p ≤ 1 / 2`
they are maximum-likelihood decoders (`Cslib.BitString.bsc_apply_toReal_le_of_isNearestDecoder`).
Achievability of the capacity `1 - h₂(p)` by random codes is in
`CslibFrontier.Probability.BitString.BinarySymmetricChannel.Achievability`.

## Main definitions

* `Cslib.BitString.bscNoise`: the noise of `BSC_p`, independent bit flips.
* `Cslib.BitString.bsc`: the binary symmetric channel.
* `Cslib.BitString.decodingError`: the error probability of a code on `BSC_p` at a message.
* `Cslib.BitString.IsNearestDecoder`: nearest-codeword decoding.

## Main results

* `Cslib.BitString.bscNoise_eq_pi`, `Cslib.BitString.bsc_eq_map`: the noise is a product of
  independent coins and the output is the input plus the noise.
* `Cslib.BitString.bscNoise_apply_toReal`, `Cslib.BitString.bsc_apply_toReal`: the masses of the
  noise and of the channel output.
* `Cslib.BitString.exists_isNearestDecoder`: nearest-codeword decoders exist.
* `Cslib.BitString.bsc_apply_toReal_le_of_isNearestDecoder`: nearest-codeword decoding is
  maximum-likelihood decoding for `p ≤ 1 / 2`.
* `Cslib.BitString.decodingError_def`, `Cslib.BitString.decodingError_eq_bernoulliAverage`: the
  error probability as a probability of the channel output and as an average over the noise.
* `Cslib.BitString.decodingError_zero_eq_zero`, `Cslib.BitString.IsNearestDecoder.leftInverse`:
  a noiseless channel never confuses the messages of an injective code.
* `Cslib.BitString.decodingError_nonneg`, `Cslib.BitString.decodingError_le_one`,
  `Cslib.BitString.decodingError_symm`: error probabilities lie in `[0, 1]`, and complementing the
  received word exchanges `BSC_p` and `BSC_{1 - p}`.
* `Cslib.BitString.bscNoise_toOuterMeasure_lt_weight_toReal`,
  `Cslib.BitString.bscNoise_toOuterMeasure_lt_weight_toReal_le`: the number of flipped bits is
  binomial, with a Hoeffding upper tail.

## References

* [C. E. Shannon, *A Mathematical Theory of Communication*][Shannon1948]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019], draft of
  26 August 2025
-/

public section

namespace Cslib.BitString

open Finset
open scoped unitInterval

variable {ι : Type*} [Fintype ι]

/-! ### The channel -/

/-- The noise of the binary symmetric channel: every coordinate is flipped independently with
probability `p`. -/
noncomputable def bscNoise (p : I) : PMF (ι → Bool) :=
  Probability.PMF.pi fun _ => Probability.PMF.coin p

/-- The noise of `BSC_p` is the product of independent coins of bias `p`, one per coordinate. -/
theorem bscNoise_eq_pi (p : I) :
    bscNoise (ι := ι) p = Probability.PMF.pi fun _ => Probability.PMF.coin p := by
  rw [bscNoise]

/-- The noise of `BSC_p` has the law of a random mask of rate `p`. -/
theorem bscNoise_apply_toReal (p : I) (e : ι → Bool) :
    (bscNoise p e).toReal = bernoulliWeight p e := by
  rw [bscNoise, Probability.PMF.pi_apply, ENNReal.toReal_prod, bernoulliWeight]
  exact prod_congr rfl fun i _ => Probability.PMF.coin_apply_toReal p (e i)

/-- The **binary symmetric channel** `BSC_p` on words `ι → Bool`: on input `x` it delivers
`x + e`, where the noise `e` flips every bit independently with probability `p`. -/
noncomputable def bsc (p : I) (x : ι → Bool) : PMF (ι → Bool) :=
  (bscNoise p).map (x + ·)

/-- `BSC_p` delivers the input plus the noise. -/
theorem bsc_eq_map (p : I) (x : ι → Bool) : bsc p x = (bscNoise p).map (x + ·) := by
  rw [bsc]

theorem bsc_apply (p : I) (x y : ι → Bool) : bsc p x y = bscNoise p (x + y) := by
  rw [bsc, PMF.map_apply, tsum_eq_single (x + y)]
  · rw [BitString.add_cancel_left, ite_eq_left rfl]
  · intro e he
    refine ite_eq_right fun hy => he ?_
    rw [hy, BitString.add_cancel_left]

/-- The channel delivers `y` on input `x` with probability `p ^ d (1 - p) ^ (n - d)`, where `d` is
the Hamming distance of `x` and `y`. -/
theorem bsc_apply_toReal (p : I) (x y : ι → Bool) :
    (bsc p x y).toReal =
      (p : ℝ) ^ hammingDist x y * (1 - p) ^ (Fintype.card ι - hammingDist x y) := by
  rw [bsc_apply, bscNoise_apply_toReal, bernoulliWeight_eq_pow_mul_pow, hammingDist_eq_weight_add]

/-- The likelihood `p ^ d (1 - p) ^ (n - d)` of `BSC_p` decreases with the distance `d` when
`p ≤ 1 / 2`. -/
theorem bsc_apply_toReal_anti (p : I) (hp : (p : ℝ) ≤ 1 / 2) {x x' y : ι → Bool}
    (h : hammingDist x y ≤ hammingDist x' y) : (bsc p x' y).toReal ≤ (bsc p x y).toReal := by
  rw [bsc_apply_toReal, bsc_apply_toReal]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le (hammingDist_le_card_fintype (x := x') (y := y))
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hpq : (p : ℝ) ≤ 1 - p := by linarith
  rw [hl, Nat.add_sub_cancel_left, hk, show hammingDist x y + k + l - hammingDist x y = k + l by
    omega, pow_add, pow_add]
  calc (p : ℝ) ^ hammingDist x y * p ^ k * (1 - p) ^ l
      ≤ (p : ℝ) ^ hammingDist x y * (1 - p) ^ k * (1 - p) ^ l := by
        have : (0 : ℝ) ≤ 1 - p := by linarith
        gcongr
    _ = _ := by ring

/-- The number of bits flipped by `BSC_p` is binomially distributed: more than `r` of the `n` bits
flip with probability `∑_{r < k ≤ n} C(n, k) p ^ k (1 - p) ^ (n - k)`. -/
theorem bscNoise_toOuterMeasure_lt_weight_toReal (p : I) (r : ℕ) :
    ((bscNoise p).toOuterMeasure {e : ι → Bool | r < weight e}).toReal =
      ∑ k ∈ range (Fintype.card ι + 1) with r < k,
        ((Fintype.card ι).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card ι - k) := by
  classical
  rw [← bernoulliAverage_lt_weight, Probability.PMF.toOuterMeasure_apply_toReal, bernoulliAverage]
  refine sum_congr rfl fun e _ => ?_
  simp only [Set.mem_ofPred_eq, bscNoise_apply_toReal, mul_ite, mul_one, mul_zero]

/-- **Hoeffding's bound on the number of flipped bits**: if `n p ≤ r + 1`, more than `r` of the
`n` bits flip with probability at most `exp (-2 (r + 1 - n p) ^ 2 / n)`. -/
theorem bscNoise_toOuterMeasure_lt_weight_toReal_le (p : I) {r : ℕ}
    (hr : Fintype.card ι * (p : ℝ) ≤ r + 1) :
    ((bscNoise p).toOuterMeasure {e : ι → Bool | r < weight e}).toReal ≤
      Real.exp (-2 * (r + 1 - Fintype.card ι * (p : ℝ)) ^ 2 / Fintype.card ι) := by
  rw [bscNoise_toOuterMeasure_lt_weight_toReal]
  have hp1 : (0 : ℝ) ≤ 1 - p := sub_nonneg.mpr p.2.2
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  refine (sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => by positivity).trans
    (sum_filter_le_sub_choose_mul_pow_le (Fintype.card ι) p.2.1 p.2.2 (sub_nonneg.mpr hr))
  obtain ⟨hk, hrk⟩ := mem_filter.mp hk
  refine mem_filter.mpr ⟨hk, ?_⟩
  have : (r + 1 : ℝ) ≤ k := by exact_mod_cast hrk
  linarith

/-! ### Codes, decoders and their errors -/

variable {M : Type*}

/-- The probability that the decoder `D` fails to recover the message `m` when its codeword
`E m` is sent through `BSC_p`. -/
noncomputable def decodingError (p : I) (E : M → ι → Bool) (D : (ι → Bool) → M) (m : M) : ℝ :=
  ((bsc p (E m)).toOuterMeasure {y | D y ≠ m}).toReal

/-- The error probability is the probability, under the channel output on `E m`, that `D` does not
return `m`. -/
theorem decodingError_def (p : I) (E : M → ι → Bool) (D : (ι → Bool) → M) (m : M) :
    decodingError p E D m = ((bsc p (E m)).toOuterMeasure {y | D y ≠ m}).toReal := by
  rw [decodingError]

/-- **Nearest-codeword decoding is maximum-likelihood decoding** on `BSC_p` for `p ≤ 1 / 2`: the
decoded codeword is at least as likely to produce the received word as any other codeword. -/
theorem bsc_apply_toReal_le_of_isNearestDecoder {E : M → ι → Bool} {D : (ι → Bool) → M}
    (hD : IsNearestDecoder E D) (p : I) (hp : (p : ℝ) ≤ 1 / 2) (y : ι → Bool) (m : M) :
    (bsc p (E m) y).toReal ≤ (bsc p (E (D y)) y).toReal :=
  bsc_apply_toReal_anti p hp (hD y m)

variable [DecidableEq ι]

/-- The error probability of a code at `m` is the probability, over the noise `e` of `BSC_p`, that
`D` does not decode `E m + e` to `m`. -/
theorem decodingError_eq_bernoulliAverage [DecidableEq M] (p : I) (E : M → ι → Bool)
    (D : (ι → Bool) → M) (m : M) :
    decodingError p E D m =
      bernoulliAverage p (fun e => if D (E m + e) ≠ m then 1 else 0) := by
  rw [decodingError, Probability.PMF.toOuterMeasure_apply_toReal, bernoulliAverage]
  refine (Fintype.sum_equiv (Equiv.addLeft (E m)) _ _ fun e => ?_).symm
  simp only [Equiv.coe_addLeft, Set.mem_ofPred_eq, bsc_apply, BitString.add_cancel_left,
    bscNoise_apply_toReal, mul_ite, mul_one, mul_zero]

omit [DecidableEq ι] in
/-- Error probabilities are nonnegative. -/
theorem decodingError_nonneg (p : I) (E : M → ι → Bool) (D : (ι → Bool) → M) (m : M) :
    0 ≤ decodingError p E D m := by
  classical
  rw [decodingError_eq_bernoulliAverage]
  simpa only [bernoulliAverage_const] using
    bernoulliAverage_mono p.2.1 p.2.2 (f := fun _ => 0) fun e => by split_ifs <;> norm_num

omit [DecidableEq ι] in
/-- Error probabilities are at most one. -/
theorem decodingError_le_one (p : I) (E : M → ι → Bool) (D : (ι → Bool) → M) (m : M) :
    decodingError p E D m ≤ 1 := by
  classical
  rw [decodingError_eq_bernoulliAverage]
  simpa only [bernoulliAverage_const] using
    bernoulliAverage_mono p.2.1 p.2.2 (g := fun _ => 1) fun e => by split_ifs <;> norm_num

omit [DecidableEq ι] in
/-- **Flipping every received bit turns `BSC_p` into `BSC_{1 - p}`**: a decoder `D` errs on `BSC_p`
exactly as often as the decoder that first complements the received word errs on `BSC_{1 - p}`. -/
theorem decodingError_symm (p : I) (E : M → ι → Bool) (D : (ι → Bool) → M) (m : M) :
    decodingError (σ p) E (fun y => D fun i => !y i) m = decodingError p E D m := by
  classical
  rw [decodingError_eq_bernoulliAverage, decodingError_eq_bernoulliAverage,
    unitInterval.coe_symm_eq, bernoulliAverage_one_sub]
  congr 1 with e : 1
  have h : (fun i => !(E m + fun i => !e i) i) = E m + e := by
    funext i
    change (!(E m i ^^ !e i)) = (E m i ^^ e i)
    cases E m i <;> cases e i <;> rfl
  rw [h]

omit [DecidableEq ι] in
/-- Over the noiseless channel `BSC_0`, a decoder that inverts the encoder never errs. -/
theorem decodingError_zero_eq_zero {E : M → ι → Bool} {D : (ι → Bool) → M}
    (hDE : Function.LeftInverse D E) (m : M) : decodingError 0 E D m = 0 := by
  classical
  rw [decodingError_eq_bernoulliAverage, Set.Icc.coe_zero, bernoulliAverage_zero]
  have h : E m + (fun _ => false) = E m := funext fun i => Bool.xor_false (E m i)
  rw [h, hDE m, ite_eq_right fun h => h rfl]

end Cslib.BitString
