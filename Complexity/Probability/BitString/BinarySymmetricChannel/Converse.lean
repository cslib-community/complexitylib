/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.BitString.BinarySymmetricChannel
public import Complexity.Probability.Entropy.Fano
public import Complexity.Probability.MutualInformation
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Order.Filter.AtTopBot.Defs
import Complexity.Foundations.Data.BitString.Basic
import Complexity.Probability.Entropy.Pi
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Map
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Shannon's coding theorem for the binary symmetric channel: the weak converse

No code transmits reliably over the binary symmetric channel `BSC_p` at a rate above its capacity
`1 - h₂(p)`, where `h₂(p) = Real.binEntropy p / Real.log 2` is the binary entropy in bits: the
**weak converse** of Shannon's noisy-channel coding theorem for `BSC_p`, in the form of
[Cover and Thomas, Theorem 7.9.1][CoverThomas2006] specialized to `BSC_p`.

A code is an encoder `E : M → (ι → Bool)` with any decoder `D : (ι → Bool) → M`, and its average
error probability is `Pe = 𝔼 m, decodingError p E D m`, the error probability of a uniformly random
message. Sending a uniform message `W` through `BSC_p` gives a joint law of `W` and the received
word `Y`. Then:

* `I(W; Y) ≤ n (1 - h₂(p))` (`Cslib.BitString.mutualInfo_bind_bsc_le`), because `H(Y) ≤ n` and
  `H(Y | W) = n h₂(p)`: whatever is sent, the output is a translate of the noise, an independent
  product of `n` coins of entropy `h₂(p)` (`Cslib.BitString.entropy_bsc`). The bound holds for any
  input law, with equality for uniform inputs
  (`Cslib.BitString.mutualInfo_uniformOfFintype_bind_bsc`), so `1 - h₂(p)` is the capacity per
  channel use [Cover and Thomas, Section 7.1][CoverThomas2006].
  This additive-noise argument replaces the chain rule for `n` uses of a memoryless channel
  [Cover and Thomas, Lemma 7.9.2][CoverThomas2006], which is not needed for `BSC_p`.
* Fano's inequality bounds `H(W | Y) ≤ h₂(Pe) + Pe log₂ (|M| - 1)`
  (`Cslib.Probability.PMF.conditionalEntropy_le_binEntropy_add_mul_logb`).

Since `log₂ |M| = H(W) = I(W; Y) + H(W | Y)`, every code satisfies
`log₂ |M| ≤ n (1 - h₂(p)) + h₂(Pe) + Pe log₂ (|M| - 1)` (`Cslib.BitString.logb_card_le_add_fano`)
and hence `(1 - Pe) log₂ |M| ≤ n (1 - h₂(p)) + 1`
(`Cslib.BitString.one_sub_expect_decodingError_mul_logb_card_le`), the source's
`R ≤ Pe R + 1/n + C`. At a rate `R > 1 - h₂(p)` the average error is therefore at least
`(R - (1 - h₂(p))) / (2 R)` once `n ≥ 2 / (R - (1 - h₂(p)))`
(`Cslib.BitString.le_expect_decodingError_of_lt_rate`,
`Cslib.BitString.eventually_le_expect_decodingError`). The maximal error is at least the average.

The results hold for every `p ∈ [0, 1]` and every deterministic decoder, not only nearest-codeword
decoders. With `Cslib.BitString.eventually_exists_code_decodingError_le` they show that
`1 - h₂(p)` is the capacity of `BSC_p` for `p < 1 / 2`. The strong converse (the error tends to `1`
above capacity, [Guruswami, Rudra and Sudan, Theorem 6.3.1(2)][GuruswamiRudraSudan2019]), general
discrete memoryless channels and channels with feedback are not formalized here.

## Main results

* `Cslib.BitString.entropy_flipBit`, `Cslib.BitString.entropy_bscNoise`,
  `Cslib.BitString.entropy_bsc`: the noise of `BSC_p` on `n` bits has entropy `n h₂(p)`.
* `Cslib.BitString.mutualInfo_bind_bsc_le`: `n` uses of `BSC_p` carry at most `n (1 - h₂(p))` bits.
* `Cslib.BitString.mutualInfo_uniformOfFintype_bind_bsc`: equality for uniform inputs.
* `Cslib.BitString.logb_card_le_add_fano`: the converse with Fano's inequality.
* `Cslib.BitString.one_sub_expect_decodingError_mul_logb_card_le`: the weak converse.
* `Cslib.BitString.le_expect_decodingError_of_lt_rate`,
  `Cslib.BitString.eventually_le_expect_decodingError`: above capacity the average error is
  bounded away from zero.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], 2nd ed.,
  Sections 7.1 and 7.9.
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019], draft of
  26 August 2025
-/

public section

namespace Cslib.BitString

open Finset Cslib.Probability.PMF
open scoped BigOperators unitInterval

variable {ι : Type*} [Fintype ι] {M : Type*}

/-! ### Entropy of the noise -/

/-- A bit flipped with probability `p` carries `h₂(p)` bits of entropy. -/
theorem entropy_flipBit (p : I) : entropy (flipBit p) = Real.binEntropy p / Real.log 2 := by
  rw [entropy_bool, flipBit_apply_toReal, ite_eq_left rfl]

/-- The noise of `BSC_p` on `n` bits has entropy `n h₂(p)`. -/
theorem entropy_bscNoise (p : I) :
    entropy (bscNoise (ι := ι) p) = Fintype.card ι * (Real.binEntropy p / Real.log 2) := by
  rw [bscNoise_eq_pi, entropy_pi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, entropy_flipBit]

/-- Whatever is sent, the output of `BSC_p` on `n` bits has entropy `n h₂(p)`. -/
theorem entropy_bsc (p : I) (x : ι → Bool) :
    entropy (bsc p x) = Fintype.card ι * (Real.binEntropy p / Real.log 2) := by
  rw [bsc_eq_map, entropy_map_of_injective _ (add_right_injective x), entropy_bscNoise]

/-! ### Mutual information across the channel -/

/-- **`n` uses of `BSC_p` carry at most `n (1 - h₂(p))` bits**: if a message `W` drawn from any law
`ν` is encoded by `E` and sent through `BSC_p`, the mutual information of `W` and the received word
is at most `n (1 - h₂(p))`. -/
theorem mutualInfo_bind_bsc_le {Ω : Type*} [Finite Ω] (p : I) (ν : PMF Ω) (E : Ω → ι → Bool) :
    mutualInfo (ν.bind fun m => (bsc p (E m)).map (m, ·)) ≤
      Fintype.card ι * (1 - Real.binEntropy p / Real.log 2) := by
  classical
  let := Fintype.ofFinite Ω
  have hcond := conditionalEntropy_bind_pair ν (fun m => bsc p (E m))
  simp only [entropy_bsc, ← Finset.sum_mul, sum_toReal, one_mul] at hcond
  have hY := entropy_le_log_card ((ν.bind fun m => (bsc p (E m)).map (m, ·)).map Prod.snd)
  rw [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_two, Real.logb_pow,
    Real.logb_self_eq_one one_lt_two, mul_one] at hY
  rw [mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy, mul_sub, mul_one]
  linarith

/-- The output of `BSC_p` on a uniformly random input is uniform. -/
private theorem map_snd_uniformOfFintype_bind_bsc [DecidableEq ι] (p : I) :
    ((Probability.PMF.uniformOfFintype (ι → Bool)).bind fun x => (bsc p x).map (x, ·)).map
      Prod.snd = Probability.PMF.uniformOfFintype (ι → Bool) := by
  classical
  have hmap : ∀ x : ι → Bool, ((bsc p x).map (x, ·)).map Prod.snd = bsc p x := fun x => by
    rw [PMF.map_comp]
    exact PMF.map_id _
  rw [PMF.map_bind]
  simp only [hmap]
  ext y
  rw [PMF.bind_apply, tsum_fintype]
  simp only [Probability.PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum]
  conv_rhs => rw [← mul_one ((Fintype.card (ι → Bool) : ENNReal)⁻¹)]
  congr 1
  simp only [bsc_apply]
  rw [Fintype.sum_equiv (Equiv.addRight y) (fun x => bscNoise p (x + y)) (bscNoise p)
    (fun x => rfl)]
  simpa only [tsum_fintype] using (bscNoise (ι := ι) p).tsum_coe

/-- On a uniformly random input, `n` uses of `BSC_p` carry exactly `n (1 - h₂(p))` bits, so the
bound `Cslib.BitString.mutualInfo_bind_bsc_le` is attained: `1 - h₂(p)` is the capacity of `BSC_p`
per channel use [Cover and Thomas, Section 7.1][CoverThomas2006]. -/
theorem mutualInfo_uniformOfFintype_bind_bsc [DecidableEq ι] (p : I) :
    mutualInfo
        ((Probability.PMF.uniformOfFintype (ι → Bool)).bind fun x => (bsc p x).map (x, ·)) =
      Fintype.card ι * (1 - Real.binEntropy p / Real.log 2) := by
  classical
  have hcond := conditionalEntropy_bind_pair (Probability.PMF.uniformOfFintype (ι → Bool))
    (fun x => bsc p x)
  simp only [entropy_bsc, ← Finset.sum_mul, sum_toReal, one_mul] at hcond
  rw [mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy, map_snd_uniformOfFintype_bind_bsc]
  have hU : entropy (Probability.PMF.uniformOfFintype (ι → Bool)) = Fintype.card ι := by
    rw [entropy_uniform, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_two,
      Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
  rw [hU, hcond, mul_sub, mul_one]

/-! ### The converse -/

/-- **The converse with Fano's inequality**: every code `E : M → (ι → Bool)` for `BSC_p` with a
decoder `D` and average error probability `Pe` satisfies
`log₂ |M| ≤ n (1 - h₂(p)) + h₂(Pe) + Pe log₂ (|M| - 1)`, where `n = |ι|`. -/
theorem logb_card_le_add_fano [Fintype M] [Nonempty M] (p : I) (E : M → ι → Bool)
    (D : (ι → Bool) → M) :
    Real.logb 2 (Fintype.card M) ≤
      Fintype.card ι * (1 - Real.binEntropy p / Real.log 2) +
        Real.binEntropy (𝔼 m, decodingError p E D m) / Real.log 2 +
          (𝔼 m, decodingError p E D m) * Real.logb 2 (Fintype.card M - 1) := by
  classical
  -- the probability that `D` misdecodes a uniform message is the average error
  have hPe : ((((Probability.PMF.uniformOfFintype M).bind fun m =>
      (bsc p (E m)).map (m, ·)).map Prod.swap).toOuterMeasure {z | D z.1 ≠ z.2}).toReal =
        𝔼 m, decodingError p E D m := by
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_bind_apply, tsum_fintype]
    simp only [PMF.toOuterMeasure_map_apply, Probability.PMF.uniformOfFintype_apply]
    rw [← Finset.mul_sum, ENNReal.toReal_mul,
      ENNReal.toReal_sum (fun m _ => toOuterMeasure_ne_top _ _), Finset.expect_eq_sum_div_card,
      Finset.card_univ, ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_mul_eq_div]
    simp only [decodingError_eq]
    rfl
  have hI := mutualInfo_bind_bsc_le p (Probability.PMF.uniformOfFintype M) E
  have hF := conditionalEntropy_le_binEntropy_add_mul_logb
    (((Probability.PMF.uniformOfFintype M).bind fun m => (bsc p (E m)).map (m, ·)).map Prod.swap) D
  rw [hPe] at hF
  set J := (Probability.PMF.uniformOfFintype M).bind fun m => (bsc p (E m)).map (m, ·) with hJ
  have hswap : entropy (J.map Prod.swap) = entropy J :=
    entropy_map_of_injective J Prod.swap_injective
  have hfst : (J.map Prod.swap).map Prod.fst = J.map Prod.snd := by
    rw [PMF.map_comp]
    rfl
  have hM : entropy (J.map Prod.fst) = Real.logb 2 (Fintype.card M) := by
    rw [hJ, map_fst_bind_pair, entropy_uniform]
  have hI' := mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy J
  rw [conditionalEntropy, hswap, hfst] at hF
  rw [conditionalEntropy, hM] at hI'
  linarith

/-- **The weak converse for `BSC_p`** [Cover and Thomas, Theorem 7.9.1][CoverThomas2006]: every code
`E : M → (ι → Bool)` with a decoder `D` and average error probability `Pe` satisfies
`(1 - Pe) log₂ |M| ≤ n (1 - h₂(p)) + 1`. For a code of rate `R = log₂ |M| / n` this is
`R ≤ Pe R + 1 / n + (1 - h₂(p))`. -/
theorem one_sub_expect_decodingError_mul_logb_card_le [Fintype M] [Nonempty M] (p : I)
    (E : M → ι → Bool) (D : (ι → Bool) → M) :
    (1 - 𝔼 m, decodingError p E D m) * Real.logb 2 (Fintype.card M) ≤
      Fintype.card ι * (1 - Real.binEntropy p / Real.log 2) + 1 := by
  have h := logb_card_le_add_fano p E D
  set Pe := 𝔼 m, decodingError p E D m
  have hPe0 : 0 ≤ Pe := Finset.expect_nonneg fun m _ => by
    rw [decodingError_eq]
    exact ENNReal.toReal_nonneg
  have hh : Real.binEntropy Pe / Real.log 2 ≤ 1 := by
    rw [div_le_one (Real.log_pos one_lt_two)]
    exact Real.binEntropy_le_log_two
  have hcard : (1 : ℝ) ≤ Fintype.card M := by exact_mod_cast Fintype.card_pos
  have hlog : Real.logb 2 (Fintype.card M - 1) ≤ Real.logb 2 (Fintype.card M) := by
    rcases eq_or_lt_of_le hcard with h1 | h1
    · rw [← h1, sub_self, Real.logb_zero, Real.logb_one]
    · exact Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_left hlog hPe0
  linarith

/-- **Above capacity the error is bounded away from zero**, finite form: if
`R > 1 - h₂(p)`, a code has `log₂ |M| ≥ R n` messages and `n ≥ 2 / (R - (1 - h₂(p)))`, then its
average error probability is at least `(R - (1 - h₂(p))) / (2 R)`, for every decoder. -/
theorem le_expect_decodingError_of_lt_rate [Fintype M] [Nonempty M] (p : I) {R : ℝ}
    (hR : 1 - Real.binEntropy p / Real.log 2 < R)
    (hM : R * Fintype.card ι ≤ Real.logb 2 (Fintype.card M))
    (hn : 2 ≤ (R - (1 - Real.binEntropy p / Real.log 2)) * Fintype.card ι)
    (E : M → ι → Bool) (D : (ι → Bool) → M) :
    (R - (1 - Real.binEntropy p / Real.log 2)) / (2 * R) ≤ 𝔼 m, decodingError p E D m := by
  have h := one_sub_expect_decodingError_mul_logb_card_le p E D
  set C := 1 - Real.binEntropy p / Real.log 2 with hC
  set Pe := 𝔼 m, decodingError p E D m
  set n : ℝ := (Fintype.card ι : ℝ)
  have hC0 : 0 ≤ C := by
    rw [hC, sub_nonneg, div_le_one (Real.log_pos one_lt_two)]
    exact Real.binEntropy_le_log_two
  have hR0 : 0 < R := hC0.trans_lt hR
  rw [div_le_iff₀ (by positivity)]
  by_cases hPe1 : Pe ≤ 1
  · have h1 : (1 - Pe) * (R * n) ≤ (1 - Pe) * Real.logb 2 (Fintype.card M) :=
      mul_le_mul_of_nonneg_left hM (sub_nonneg.mpr hPe1)
    have hn0 : 0 < n := pos_of_mul_pos_right (by linarith) (sub_pos.mpr hR).le
    refine le_of_mul_le_mul_right ?_ hn0
    linarith
  · have := mul_pos (sub_pos.mpr (not_le.mp hPe1)) hR0
    linarith

open Filter in
/-- **Shannon's noisy-channel coding theorem for the binary symmetric channel, weak converse**, in
its asymptotic form: for every `p ∈ [0, 1]` and every rate `R > 1 - h₂(p)`, for all sufficiently
large `n` every code with `2 ^ ⌈R n⌉₊` codewords of length `n` has average error probability at
least `(R - (1 - h₂(p))) / (2 R) > 0`, under every decoder. -/
theorem eventually_le_expect_decodingError (p : I) {R : ℝ}
    (hR : 1 - Real.binEntropy p / Real.log 2 < R) :
    ∀ᶠ n : ℕ in atTop, ∀ (E : Fin (2 ^ ⌈R * n⌉₊) → BitString n)
      (D : BitString n → Fin (2 ^ ⌈R * n⌉₊)),
      (R - (1 - Real.binEntropy p / Real.log 2)) / (2 * R) ≤ 𝔼 m, decodingError p E D m := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 / (R - (1 - Real.binEntropy p / Real.log 2)))
  filter_upwards [eventually_ge_atTop N] with n hn E D
  have : Nonempty (Fin (2 ^ ⌈R * n⌉₊)) := ⟨⟨0, by positivity⟩⟩
  refine le_expect_decodingError_of_lt_rate p hR ?_ ?_ E D
  · rw [Fintype.card_fin, Fintype.card_fin, Nat.cast_pow, Nat.cast_two, Real.logb_pow,
      Real.logb_self_eq_one one_lt_two, mul_one]
    exact Nat.le_ceil _
  · rw [Fintype.card_fin]
    have hRC := sub_pos.mpr hR
    have h2 : 2 / (R - (1 - Real.binEntropy p / Real.log 2)) ≤ n :=
      hN.trans (by exact_mod_cast hn)
    rw [div_le_iff₀ hRC] at h2
    linarith

end Cslib.BitString
