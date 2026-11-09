/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.SignedDigitStream.Basic
public import CslibFrontier.Foundations.Data.Finset.KthLargest
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary stream operations, finite-state prefix comparisons, ranks, and buffered tests

This module formalizes the deterministic scaled integer approximations and low-residue window
identities for the elementary signed-digit stream operations of
[OpenAI2026LogSpace, Sections 10.2 and 10.5, Lemmas 10.3, 10.6, 10.7, and 10.8]:

1. **Public rational streams** (`ratApprox`, `ratStream`): exact integer floor approximations
   `⌊2 ^ t * r⌋` for rational constants `r : ℚ`.
2. **Low-residue locality** (`windowPrefix`, `intPrefix_emod_eq_windowPrefix_emod`): modulo
   `2 ^ W`, `intPrefix x K` depends only on the `W` digits in `Ico (K + 1 - W) (K + 1)`.
3. **27-state prefix comparison automaton** (`cmpStep`, `cmpPrefix`): scanning from place `0` to
   `K` with state clamped to `[-13, 13]` decides the exact order of `streamPrefix x K` and
   `streamPrefix y K`.
4. **Elementary operations** (`pairAvgApprox`, `maxApprox`, `minApprox`, `shiftClipApprox`):
   pair averages `(x + y) / 2`, maxima, minima, and arbitrary `2 ^ v` shifts clipped to `[-1, 1]`.
5. **Zero-padded detector ranks** (`zeroPaddedRankApprox`): `Finset.kthLargest` over stream
   prefixes at `t + 4` (which inserts `0` so negative order statistics clamp up to `0`, matching
   the detector rank of Sections 4.2 and 8.2 rather than the general signed order statistic of
   Lemma 10.6), with error `< 2` by `Finset.abs_kthLargest_sub_kthLargest_le`.
6. **Buffered margin tests** (`cmpBuffered`, `bufferedTest`): 63-state finite-precision test
   accepting all `s > 2 u` and rejecting all `s ≤ u` when `u ≥ ρ ≥ 2 ^ (-R)`.

## Main definitions

* `Cslib.SignedDigitStream.ratApprox`, `Cslib.SignedDigitStream.ratStream`: rational streams.
* `Cslib.SignedDigitStream.windowPrefix`: bounded-window suffix of `intPrefix`.
* `Cslib.SignedDigitStream.cmpStep`, `Cslib.SignedDigitStream.cmpPrefix`: `[-13, 13]` prefix
  comparator.
* `Cslib.SignedDigitStream.pairAvgApprox`, `Cslib.SignedDigitStream.maxApprox`,
  `Cslib.SignedDigitStream.minApprox`, `Cslib.SignedDigitStream.shiftClipApprox`: scaled integer
  approximations for elementary operations and shifts with clipping.
* `Cslib.SignedDigitStream.zeroPaddedRankApprox`: scaled integer approximation for the zero-padded
  detector rank `Finset.kthLargest`.
* `Cslib.SignedDigitStream.cmpBuffered`, `Cslib.SignedDigitStream.bufferedTest`: fixed-precision
  buffered margin test.

## Main results

* `Cslib.SignedDigitStream.intPrefix_emod_eq_windowPrefix_emod`: low-residue locality.
* `Cslib.SignedDigitStream.cmpPrefix_eq_clamp_sub`, `Cslib.SignedDigitStream.cmpPrefix_pos_iff`:
  exactness of the 27-state prefix comparison automaton.
* `Cslib.SignedDigitStream.pairAvgApprox_isScaledApprox`,
  `Cslib.SignedDigitStream.maxApprox_isScaledApprox`,
  `Cslib.SignedDigitStream.minApprox_isScaledApprox`,
  `Cslib.SignedDigitStream.shiftClipApprox_isScaledApprox`,
  `Cslib.SignedDigitStream.zeroPaddedRankApprox_isScaledApprox`: `< 2` scaled approximation
  bounds.
* `Cslib.SignedDigitStream.bufferedTest_eq_true_of_two_mul_lt`,
  `Cslib.SignedDigitStream.bufferedTest_eq_false_of_le`: soundness of buffered margin tests.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 10.2 and 10.5, Lemmas 10.3 and 10.6--10.8 (23 September 2026, revision `7ef5c0cc`,
  not peer reviewed).
-/

public section

namespace Cslib.SignedDigitStream

open Finset

/-- Euclidean floor quotient `A / M` approximates the real quotient `(A : ℝ) / M` within `< 1`. -/
theorem abs_ediv_sub_div_lt_one (A : ℤ) {M : ℤ} (hM : 0 < M) :
    |((A / M : ℤ) : ℝ) - (A : ℝ) / (M : ℝ)| < 1 := by
  have hM_real : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hdiv : M * (A / M) + A % M = A := by linarith [Int.emod_def A M]
  have hr0 : (0 : ℝ) ≤ ((A % M : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg A hM.ne'
  have hrlt : ((A % M : ℤ) : ℝ) < (M : ℝ) := by exact_mod_cast Int.emod_lt_of_pos A hM
  have hreal : (M : ℝ) * ((A / M : ℤ) : ℝ) + ((A % M : ℤ) : ℝ) = (A : ℝ) := by
    exact_mod_cast hdiv
  have heq : ((A / M : ℤ) : ℝ) - (A : ℝ) / (M : ℝ) = -(((A % M : ℤ) : ℝ) / (M : ℝ)) := by
    field_simp
    linarith
  rw [heq, abs_neg, abs_div, abs_of_nonneg hr0, abs_of_pos hM_real]
  exact (div_lt_one hM_real).mpr hrlt

/-- Closing step of the scaled floor-quotient approximations: if `A / M = 2 ^ t * P` over `ℝ` and
`2 ^ t * P` is within `3 / 8` of `2 ^ t * Z`, then the floor quotient `A / M` is within scaled
error `< 2` of `2 ^ t * Z`. -/
private theorem abs_ediv_sub_lt_two_of_scaled (A : ℤ) {M : ℕ} (hM : 0 < M) {t : ℕ} {P Z : ℝ}
    (hA : (A : ℝ) / M = (2 : ℝ) ^ t * P)
    (herr : |(2 : ℝ) ^ t * P - (2 : ℝ) ^ t * Z| ≤ 3 / 8) :
    |((A / M : ℤ) : ℝ) - (2 : ℝ) ^ t * Z| < 2 := by
  have hfl := abs_ediv_sub_div_lt_one A (Int.natCast_pos.mpr hM)
  rw [Int.cast_natCast, hA] at hfl
  have htri := abs_sub_le ((A / M : ℤ) : ℝ) ((2 : ℝ) ^ t * P) ((2 : ℝ) ^ t * Z)
  linarith

/-- Scaled error of the prefix approximations at `K = t + 4`: if `|P - Z| ≤ 6 / 2 ^ (t + 4)`, then
`2 ^ t * P` is within `3 / 8` of `2 ^ t * Z`. -/
private theorem abs_two_pow_mul_sub_le_of_prefix {t : ℕ} {P Z : ℝ}
    (h : |P - Z| ≤ 6 / (2 : ℝ) ^ (t + 4)) :
    |(2 : ℝ) ^ t * P - (2 : ℝ) ^ t * Z| ≤ 3 / 8 := by
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ t)]
  calc (2 : ℝ) ^ t * |P - Z| ≤ (2 : ℝ) ^ t * (6 / (2 : ℝ) ^ (t + 4)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 3 / 8 := by
        have hpow : (2 : ℝ) ^ (t + 4) = 16 * (2 : ℝ) ^ t := by ring
        rw [hpow]
        field_simp
        ring

section RationalStreams

/-- Exact integer floor approximation `(2 ^ t * r.num) / r.den` for a rational constant `r`. -/
@[expose] def ratApprox (r : ℚ) (t : ℕ) : ℤ :=
  ⌊(2 : ℚ) ^ t * r⌋

/-- Computable signed-digit stream representing a rational constant `r ∈ [-1, 1]`. -/
@[expose] def ratStream (r : ℚ) : ℕ → ℤ :=
  diffDigit (ratApprox r)

theorem ratApprox_eq_ediv (r : ℚ) (t : ℕ) :
    ratApprox r t = ((2 : ℤ) ^ t * r.num) / (r.den : ℤ) := by
  unfold ratApprox
  rw [Int.floor_eq_iff]
  set d : ℤ := ((2 : ℤ) ^ t * r.num) / (r.den : ℤ)
  have hden : (0 : ℤ) < (r.den : ℤ) := by exact_mod_cast r.pos
  have hden_q : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.pos
  have hdiv : (r.den : ℤ) * d + ((2 : ℤ) ^ t * r.num) % (r.den : ℤ) = (2 : ℤ) ^ t * r.num := by
    dsimp [d]
    linarith [Int.emod_def ((2 : ℤ) ^ t * r.num) (r.den : ℤ)]
  have hr0 : 0 ≤ ((2 : ℤ) ^ t * r.num) % (r.den : ℤ) := Int.emod_nonneg _ hden.ne'
  have hrlt : ((2 : ℤ) ^ t * r.num) % (r.den : ℤ) < (r.den : ℤ) := Int.emod_lt_of_pos _ hden
  have hq : (2 : ℚ) ^ t * r = (((2 : ℤ) ^ t * r.num : ℤ) : ℚ) / (r.den : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den r]
    push_cast
    ring
  rw [hq]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hden_q]
    have hle_int : d * (r.den : ℤ) ≤ (2 : ℤ) ^ t * r.num := by
      have hcomm : d * (r.den : ℤ) = (r.den : ℤ) * d := mul_comm _ _
      omega
    exact_mod_cast hle_int
  · rw [div_lt_iff₀ hden_q]
    have hlt_int : (2 : ℤ) ^ t * r.num < (d + 1) * (r.den : ℤ) := by
      have hcomm : (d + 1) * (r.den : ℤ) = (r.den : ℤ) * d + (r.den : ℤ) := by ring
      omega
    have hcast : (((2 : ℤ) ^ t * r.num : ℤ) : ℚ) < (((d + 1) * (r.den : ℤ) : ℤ) : ℚ) := by
      exact_mod_cast hlt_int
    simpa only [Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast] using hcast

theorem ratApprox_isScaledApprox (r : ℚ) : IsScaledApprox (r : ℝ) (ratApprox r) := by
  intro t
  unfold ratApprox
  set q : ℚ := (2 : ℚ) ^ t * r
  have hle : ((⌊q⌋ : ℤ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast Int.floor_le q
  have hlt : (q : ℝ) < ((⌊q⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast Int.lt_floor_add_one q
  have hq : (q : ℝ) = (2 : ℝ) ^ t * (r : ℝ) := by
    dsimp [q]
    push_cast
    rfl
  rw [← hq, abs_lt]
  constructor <;> linarith

theorem ratStream_isSignedStream {r : ℚ} (hr : |r| ≤ 1) : IsSignedStream (ratStream r) := by
  have hreal : |(r : ℝ)| ≤ 1 := by exact_mod_cast hr
  exact diffDigit_isSignedStream hreal (ratApprox_isScaledApprox r)

theorem streamVal_ratStream {r : ℚ} (hr : |r| ≤ 1) : streamVal (ratStream r) = (r : ℝ) := by
  have hreal : |(r : ℝ)| ≤ 1 := by exact_mod_cast hr
  exact streamVal_diffDigit hreal (ratApprox_isScaledApprox r)

end RationalStreams

section ResidueWindow

/-- Windowed integer prefix summing only digits `j ∈ Ico lo (K + 1)` at scale `2 ^ K`. -/
@[expose] def windowPrefix (x : ℕ → ℤ) (lo K : ℕ) : ℤ :=
  ∑ j ∈ Ico lo (K + 1), x j * (2 : ℤ) ^ (K - j)

/-- **Low-residue locality** [OpenAI2026LogSpace, Lemma 10.3]: modulo `2 ^ W`, `intPrefix x K`
depends only on the at most `W` digits in `Ico (K + 1 - W) (K + 1)`. -/
theorem intPrefix_emod_eq_windowPrefix_emod (x : ℕ → ℤ) (K W : ℕ) :
    intPrefix x K % (2 : ℤ) ^ W = windowPrefix x (K + 1 - W) K % (2 : ℤ) ^ W := by
  unfold intPrefix windowPrefix
  have hle : K + 1 - W ≤ K + 1 := Nat.sub_le _ _
  rw [Finset.range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le (K + 1 - W)) hle]
  have hdvd : (2 : ℤ) ^ W ∣ ∑ j ∈ Ico 0 (K + 1 - W), x j * (2 : ℤ) ^ (K - j) := by
    refine dvd_sum fun j hj => ?_
    have hjlt : j < K + 1 - W := (mem_Ico.mp hj).2
    have hWle : W ≤ K - j := by omega
    exact dvd_mul_of_dvd_right (pow_dvd_pow 2 hWle) (x j)
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Int.mul_add_emod_self_left]

end ResidueWindow

section PrefixComparison

/-- Transition step of the 27-state absorbing prefix comparison automaton on `[-13, 13]`. -/
@[expose] def cmpStep (p δ : ℤ) : ℤ :=
  max (-13) (min 13 (2 * p + δ))

/-- Streaming comparison of `x^{[K]}` and `y^{[K]}` using states in `{-13, ..., 13}`
[OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def cmpPrefix (x y : ℕ → ℤ) : ℕ → ℤ
  | 0 => cmpStep 0 (x 0 - y 0)
  | K + 1 => cmpStep (cmpPrefix x y K) (x (K + 1) - y (K + 1))

theorem cmpStep_mem_Icc (p δ : ℤ) : cmpStep p δ ∈ Set.Icc (-13 : ℤ) 13 := by
  unfold cmpStep
  refine ⟨le_max_left _ _, max_le (by decide) (min_le_left _ _)⟩

theorem cmpPrefix_mem_Icc (x y : ℕ → ℤ) (K : ℕ) :
    cmpPrefix x y K ∈ Set.Icc (-13 : ℤ) 13 := by
  cases K <;> exact cmpStep_mem_Icc _ _

/-- **Exactness of the 27-state prefix comparator** [OpenAI2026LogSpace, Lemma 10.3]: for valid
signed-digit streams, `cmpPrefix x y K` equals `intPrefix x K - intPrefix y K` clamped to
`[-13, 13]`. -/
theorem cmpPrefix_eq_clamp_sub {x y : ℕ → ℤ} (hx : IsSignedStream x) (hy : IsSignedStream y)
    (K : ℕ) :
    cmpPrefix x y K = max (-13) (min 13 (intPrefix x K - intPrefix y K)) := by
  induction K with
  | zero =>
    simp [cmpPrefix, cmpStep, intPrefix_zero]
  | succ K ih =>
    rw [cmpPrefix, ih, intPrefix_succ, intPrefix_succ]
    unfold cmpStep
    have hxK := isSignedDigit_iff_le.mp (hx (K + 1))
    have hyK := isSignedDigit_iff_le.mp (hy (K + 1))
    set D := intPrefix x K - intPrefix y K
    set δ := x (K + 1) - y (K + 1)
    have hdiff : (2 * intPrefix x K + x (K + 1)) - (2 * intPrefix y K + y (K + 1)) =
        2 * D + δ := by ring
    rw [hdiff]
    omega

theorem cmpPrefix_pos_iff {x y : ℕ → ℤ} (hx : IsSignedStream x) (hy : IsSignedStream y)
    (K : ℕ) :
    0 < cmpPrefix x y K ↔ streamPrefix y K < streamPrefix x K := by
  rw [cmpPrefix_eq_clamp_sub hx hy K, streamPrefix_eq_intPrefix_div, streamPrefix_eq_intPrefix_div,
    div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < (2 : ℝ) ^ K)]
  have hint : ((intPrefix y K : ℝ) < (intPrefix x K : ℝ)) ↔ intPrefix y K < intPrefix x K :=
    Int.cast_lt
  rw [hint]
  omega

theorem cmpPrefix_neg_iff {x y : ℕ → ℤ} (hx : IsSignedStream x) (hy : IsSignedStream y)
    (K : ℕ) :
    cmpPrefix x y K < 0 ↔ streamPrefix x K < streamPrefix y K := by
  rw [cmpPrefix_eq_clamp_sub hx hy K, streamPrefix_eq_intPrefix_div, streamPrefix_eq_intPrefix_div,
    div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < (2 : ℝ) ^ K)]
  have hint : ((intPrefix x K : ℝ) < (intPrefix y K : ℝ)) ↔ intPrefix x K < intPrefix y K :=
    Int.cast_lt
  rw [hint]
  omega

theorem cmpPrefix_nonneg_iff {x y : ℕ → ℤ} (hx : IsSignedStream x) (hy : IsSignedStream y)
    (K : ℕ) :
    0 ≤ cmpPrefix x y K ↔ intPrefix y K ≤ intPrefix x K := by
  rw [cmpPrefix_eq_clamp_sub hx hy K]
  omega

theorem cmpPrefix_nonpos_iff {x y : ℕ → ℤ} (hx : IsSignedStream x) (hy : IsSignedStream y)
    (K : ℕ) :
    cmpPrefix x y K ≤ 0 ↔ intPrefix x K ≤ intPrefix y K := by
  rw [cmpPrefix_eq_clamp_sub hx hy K]
  omega

end PrefixComparison

section ElementaryOperations

/-- Scaled integer approximation to `(streamVal x + streamVal y) / 2` using `K = t + 4`
[OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def pairAvgApprox (x y : ℕ → ℤ) (t : ℕ) : ℤ :=
  (intPrefix x (t + 4) + intPrefix y (t + 4)) / 32

/-- Scaled integer approximation to `max (streamVal x) (streamVal y)` using `cmpPrefix` at
`K = t + 4` [OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def maxApprox (x y : ℕ → ℤ) (t : ℕ) : ℤ :=
  (if 0 ≤ cmpPrefix x y (t + 4) then intPrefix x (t + 4) else intPrefix y (t + 4)) / 16

/-- Scaled integer approximation to `min (streamVal x) (streamVal y)` using `cmpPrefix` at
`K = t + 4` [OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def minApprox (x y : ℕ → ℤ) (t : ℕ) : ℤ :=
  (if cmpPrefix x y (t + 4) ≤ 0 then intPrefix x (t + 4) else intPrefix y (t + 4)) / 16

/-- Real `2 ^ v` scaling followed by clamping to `[-1, 1]`. -/
@[expose] noncomputable def shiftClipVal (v : ℤ) (z : ℝ) : ℝ :=
  max (-1) (min 1 ((2 : ℝ) ^ v * z))

/-- Scaled integer approximation to `shiftClipVal v (streamVal x)` [OpenAI2026LogSpace, Lemma 10.7]:
returns `0` without querying `x` when `t + v + 4 < 0`, and otherwise clamps `intPrefix x K` at
`K = (t + v + 4).toNat` to `[-2 ^ (t + 4), 2 ^ (t + 4)]` before floor-shifting by `16`. -/
@[expose] def shiftClipApprox (v : ℤ) (x : ℕ → ℤ) (t : ℕ) : ℤ :=
  if (t : ℤ) + v + 4 < 0 then 0
  else
    let K := ((t : ℤ) + v + 4).toNat
    let B := (2 : ℤ) ^ (t + 4)
    (max (-B) (min B (intPrefix x K))) / 16

theorem pairAvgApprox_isScaledApprox {x y : ℕ → ℤ}
    (hx : IsSignedStream x) (hy : IsSignedStream y) :
    IsScaledApprox ((streamVal x + streamVal y) / 2) (pairAvgApprox x y) := by
  intro t
  unfold pairAvgApprox
  set A := intPrefix x (t + 4) + intPrefix y (t + 4)
  have hA : (A : ℝ) / (32 : ℝ) =
      (2 : ℝ) ^ t * ((streamPrefix x (t + 4) + streamPrefix y (t + 4)) / 2) := by
    dsimp [A]
    rw [streamPrefix_eq_intPrefix_div, streamPrefix_eq_intPrefix_div]
    push_cast
    have hpow : (2 : ℝ) ^ (t + 4) = 16 * (2 : ℝ) ^ t := by ring
    rw [hpow]
    field_simp
    ring
  have hx_err := abs_streamVal_sub_streamPrefix_le hx (t + 4)
  have hy_err := abs_streamVal_sub_streamPrefix_le hy (t + 4)
  refine abs_ediv_sub_lt_two_of_scaled A (by decide : 0 < 32) hA
    (abs_two_pow_mul_sub_le_of_prefix ?_)
  rw [abs_sub_comm]
  have hdiff : (streamVal x + streamVal y) / 2 -
      (streamPrefix x (t + 4) + streamPrefix y (t + 4)) / 2 =
      ((streamVal x - streamPrefix x (t + 4)) + (streamVal y - streamPrefix y (t + 4))) / 2 := by
    ring
  rw [hdiff, abs_div, abs_two]
  linarith [abs_add_le (streamVal x - streamPrefix x (t + 4))
    (streamVal y - streamPrefix y (t + 4))]

theorem pairAvgApprox_emod {x y : ℕ → ℤ} (t q : ℕ) :
    pairAvgApprox x y t % (2 : ℤ) ^ q =
      ((windowPrefix x (t + 5 - (q + 5)) (t + 4) +
        windowPrefix y (t + 5 - (q + 5)) (t + 4)) % (2 : ℤ) ^ (q + 5)) / 32 := by
  unfold pairAvgApprox
  have h32 : (32 : ℤ) = (2 : ℤ) ^ 5 := by decide
  rw [h32, ediv_two_pow_emod_eq]
  congr 1
  rw [Int.add_emod, intPrefix_emod_eq_windowPrefix_emod,
    intPrefix_emod_eq_windowPrefix_emod (x := y), ← Int.add_emod]

theorem maxApprox_eq_ediv {x y : ℕ → ℤ} (hx : IsSignedStream x) (hy : IsSignedStream y)
    (t : ℕ) :
    maxApprox x y t = max (intPrefix x (t + 4)) (intPrefix y (t + 4)) / 16 := by
  unfold maxApprox
  congr 1
  by_cases h : 0 ≤ cmpPrefix x y (t + 4)
  · have hle := (cmpPrefix_nonneg_iff hx hy (t + 4)).mp h
    simp [h, max_eq_left hle]
  · have hle : intPrefix x (t + 4) ≤ intPrefix y (t + 4) := by
      have hnot := (cmpPrefix_nonneg_iff hx hy (t + 4)).not.mp h
      omega
    simp [h, max_eq_right hle]

theorem minApprox_eq_ediv {x y : ℕ → ℤ} (hx : IsSignedStream x) (hy : IsSignedStream y)
    (t : ℕ) :
    minApprox x y t = min (intPrefix x (t + 4)) (intPrefix y (t + 4)) / 16 := by
  unfold minApprox
  congr 1
  by_cases h : cmpPrefix x y (t + 4) ≤ 0
  · have hle := (cmpPrefix_nonpos_iff hx hy (t + 4)).mp h
    simp [h, min_eq_left hle]
  · have hle : intPrefix y (t + 4) ≤ intPrefix x (t + 4) := by
      have hnot := (cmpPrefix_nonpos_iff hx hy (t + 4)).not.mp h
      omega
    simp [h, min_eq_right hle]

theorem maxApprox_isScaledApprox {x y : ℕ → ℤ}
    (hx : IsSignedStream x) (hy : IsSignedStream y) :
    IsScaledApprox (max (streamVal x) (streamVal y)) (maxApprox x y) := by
  intro t
  rw [maxApprox_eq_ediv hx hy t]
  have hx_err := abs_streamVal_sub_streamPrefix_le hx (t + 4)
  have hy_err := abs_streamVal_sub_streamPrefix_le hy (t + 4)
  rw [abs_sub_comm] at hx_err hy_err
  refine abs_ediv_sub_lt_two_of_scaled _ (by decide : 0 < 16)
    (P := max (streamPrefix x (t + 4)) (streamPrefix y (t + 4))) ?_
    (abs_two_pow_mul_sub_le_of_prefix ((abs_max_sub_max_le_max _ _ _ _).trans
      (max_le hx_err hy_err)))
  rw [Int.cast_max, streamPrefix_eq_intPrefix_div, streamPrefix_eq_intPrefix_div,
    max_div_div_right (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (t + 4))]
  have hpow : (2 : ℝ) ^ (t + 4) = 16 * (2 : ℝ) ^ t := by ring
  rw [hpow]
  push_cast
  field_simp

theorem minApprox_isScaledApprox {x y : ℕ → ℤ}
    (hx : IsSignedStream x) (hy : IsSignedStream y) :
    IsScaledApprox (min (streamVal x) (streamVal y)) (minApprox x y) := by
  intro t
  rw [minApprox_eq_ediv hx hy t]
  have hx_err := abs_streamVal_sub_streamPrefix_le hx (t + 4)
  have hy_err := abs_streamVal_sub_streamPrefix_le hy (t + 4)
  rw [abs_sub_comm] at hx_err hy_err
  refine abs_ediv_sub_lt_two_of_scaled _ (by decide : 0 < 16)
    (P := min (streamPrefix x (t + 4)) (streamPrefix y (t + 4))) ?_
    (abs_two_pow_mul_sub_le_of_prefix ((abs_min_sub_min_le_max _ _ _ _).trans
      (max_le hx_err hy_err)))
  rw [Int.cast_min, streamPrefix_eq_intPrefix_div, streamPrefix_eq_intPrefix_div,
    min_div_div_right (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (t + 4))]
  have hpow : (2 : ℝ) ^ (t + 4) = 16 * (2 : ℝ) ^ t := by ring
  rw [hpow]
  push_cast
  field_simp

theorem abs_shiftClipVal_le_one (v : ℤ) (z : ℝ) : |shiftClipVal v z| ≤ 1 := by
  unfold shiftClipVal
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem abs_clamp_sub_clamp_le (a b c d : ℝ) :
    |max a (min b c) - max a (min b d)| ≤ |c - d| := by
  calc |max a (min b c) - max a (min b d)|
      ≤ max |a - a| |min b c - min b d| := abs_max_sub_max_le_max _ _ _ _
    _ = |min b c - min b d| := by simp
    _ ≤ max |b - b| |c - d| := abs_min_sub_min_le_max _ _ _ _
    _ = |c - d| := by simp

/-- **Shift-and-clip approximation** [OpenAI2026LogSpace, Lemma 10.7]: `shiftClipApprox v x`
approximates `max (-1) (min 1 (2 ^ v * streamVal x))` within scaled error `< 2`. -/
theorem shiftClipApprox_isScaledApprox (v : ℤ) {x : ℕ → ℤ} (hx : IsSignedStream x) :
    IsScaledApprox (shiftClipVal v (streamVal x)) (shiftClipApprox v x) := by
  intro t
  unfold shiftClipApprox
  split_ifs with hneg
  · have hle : (t : ℤ) + v ≤ -5 := by omega
    have hx12 : |streamVal x| ≤ 12 := abs_streamVal_le_twelve hx
    have hval_le : |shiftClipVal v (streamVal x)| ≤ |(2 : ℝ) ^ v * streamVal x| := by
      unfold shiftClipVal
      have h0 : max (-1 : ℝ) (min 1 0) = 0 := by norm_num
      simpa only [h0, sub_zero] using abs_clamp_sub_clamp_le (-1) 1 ((2 : ℝ) ^ v * streamVal x) 0
    have hpow_le : (2 : ℝ) ^ ((t : ℤ) + v) ≤ (2 : ℝ) ^ (-5 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hle
    have hprod : |(2 : ℝ) ^ t * shiftClipVal v (streamVal x)| ≤ 3 / 8 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ t)]
      calc (2 : ℝ) ^ t * |shiftClipVal v (streamVal x)|
          ≤ (2 : ℝ) ^ t * |(2 : ℝ) ^ v * streamVal x| :=
            mul_le_mul_of_nonneg_left hval_le (by positivity)
        _ = (2 : ℝ) ^ ((t : ℤ) + v) * |streamVal x| := by
            rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ v),
              zpow_add₀ (by norm_num), zpow_natCast, mul_assoc]
        _ ≤ (2 : ℝ) ^ (-5 : ℤ) * 12 := by gcongr
        _ = 3 / 8 := by norm_num
    simp only [Int.cast_zero, zero_sub, abs_neg]
    linarith
  · have hnonneg : 0 ≤ (t : ℤ) + v + 4 := not_lt.mp hneg
    set K : ℕ := ((t : ℤ) + v + 4).toNat
    have hK : (K : ℤ) = (t : ℤ) + v + 4 := Int.toNat_of_nonneg hnonneg
    set B : ℤ := (2 : ℤ) ^ (t + 4)
    set A : ℤ := max (-B) (min B (intPrefix x K))
    have hzpow : (2 : ℝ) ^ t * ((2 : ℝ) ^ v / (2 : ℝ) ^ K) = 1 / 16 := by
      rw [← zpow_natCast (2 : ℝ) t, ← zpow_natCast (2 : ℝ) K, div_eq_mul_inv,
        ← zpow_neg, ← mul_assoc, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
      have hexp : (t : ℤ) + v + -(K : ℤ) = -4 := by omega
      rw [hexp]
      norm_num
    have hscale : (intPrefix x K : ℝ) / (16 : ℝ) =
        (2 : ℝ) ^ t * ((2 : ℝ) ^ v * streamPrefix x K) := by
      rw [streamPrefix_eq_intPrefix_div]
      calc (intPrefix x K : ℝ) / (16 : ℝ)
          = (intPrefix x K : ℝ) * (1 / 16) := by ring
        _ = (intPrefix x K : ℝ) * ((2 : ℝ) ^ t * ((2 : ℝ) ^ v / (2 : ℝ) ^ K)) := by rw [hzpow]
        _ = (2 : ℝ) ^ t * ((2 : ℝ) ^ v * ((intPrefix x K : ℝ) / (2 : ℝ) ^ K)) := by ring
    have hA : (A : ℝ) / (16 : ℝ) = (2 : ℝ) ^ t * shiftClipVal v (streamPrefix x K) := by
      dsimp [A, B, shiftClipVal]
      have hB : (((2 : ℤ) ^ (t + 4) : ℤ) : ℝ) / 16 = (2 : ℝ) ^ t := by
        push_cast
        ring
      have hnegB : (-(((2 : ℤ) ^ (t + 4) : ℤ) : ℝ)) / 16 = -(2 : ℝ) ^ t := by
        push_cast
        ring
      rw [Int.cast_max, Int.cast_min, Int.cast_neg,
        ← max_div_div_right (by norm_num : (0 : ℝ) ≤ 16),
        ← min_div_div_right (by norm_num : (0 : ℝ) ≤ 16),
        hB, hnegB, hscale]
      have hmul_min := mul_min_of_nonneg (1 : ℝ) ((2 : ℝ) ^ v * streamPrefix x K)
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ t)
      have hmul_max := mul_max_of_nonneg (-1 : ℝ) (min 1 ((2 : ℝ) ^ v * streamPrefix x K))
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ t)
      rw [hmul_max, hmul_min]
      ring_nf
    have hlip : |shiftClipVal v (streamPrefix x K) - shiftClipVal v (streamVal x)| ≤
        |(2 : ℝ) ^ v * streamPrefix x K - (2 : ℝ) ^ v * streamVal x| :=
      abs_clamp_sub_clamp_le (-1) 1 _ _
    have hx_err := abs_streamVal_sub_streamPrefix_le hx K
    rw [abs_sub_comm] at hx_err
    have htrunc : |(2 : ℝ) ^ t * shiftClipVal v (streamPrefix x K) -
        (2 : ℝ) ^ t * shiftClipVal v (streamVal x)| ≤ 3 / 8 := by
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ t)]
      calc (2 : ℝ) ^ t * |shiftClipVal v (streamPrefix x K) - shiftClipVal v (streamVal x)|
          ≤ (2 : ℝ) ^ t * |(2 : ℝ) ^ v * streamPrefix x K - (2 : ℝ) ^ v * streamVal x| :=
            mul_le_mul_of_nonneg_left hlip (by positivity)
        _ = (2 : ℝ) ^ t * ((2 : ℝ) ^ v * |streamPrefix x K - streamVal x|) := by
            rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ v)]
        _ ≤ (2 : ℝ) ^ t * ((2 : ℝ) ^ v * (6 / (2 : ℝ) ^ K)) := by gcongr
        _ = 6 * ((2 : ℝ) ^ t * ((2 : ℝ) ^ v / (2 : ℝ) ^ K)) := by ring
        _ = 3 / 8 := by
            rw [hzpow]
            norm_num
    exact abs_ediv_sub_lt_two_of_scaled A (by decide : 0 < 16) hA htrunc

end ElementaryOperations

section OrderStatisticsAndBufferedTests

/-- Scaled integer approximation to the zero-padded detector rank
`Finset.kthLargest k s (fun i => streamVal (x i))` using prefixes at `K = t + 4`.
Because `Finset.kthLargest` inserts `0` [OpenAI2026LogSpace, Sections 4.2 and 8.2], negative
order statistics clamp up to `0` (unlike the general signed order statistic of
[OpenAI2026LogSpace, Lemma 10.6]). -/
@[expose] def zeroPaddedRankApprox {ι : Type*} (k : ℕ) (s : Finset ι) (x : ι → ℕ → ℤ)
    (t : ℕ) : ℤ :=
  kthLargest k s (fun i => intPrefix (x i) (t + 4)) / 16

theorem kthLargest_streamPrefix_eq_div {ι : Type*} (k : ℕ) (s : Finset ι) (x : ι → ℕ → ℤ)
    (K : ℕ) :
    kthLargest k s (fun i => streamPrefix (x i) K) =
      ((kthLargest k s (fun i => intPrefix (x i) K) : ℤ) : ℝ) / (2 : ℝ) ^ K := by
  classical
  have hpos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  set φ : ℤ → ℝ := fun a => (a : ℝ) / (2 : ℝ) ^ K
  have hmono : StrictMono φ := fun a b hab =>
    div_lt_div_of_pos_right (Int.cast_lt.mpr hab) hpos
  have hfilt : (s.filter fun i => k ≤ #{w ∈ s | streamPrefix (x i) K ≤ streamPrefix (x w) K}) =
      (s.filter fun i => k ≤ #{w ∈ s | intPrefix (x i) K ≤ intPrefix (x w) K}) := by
    ext i
    simp only [mem_filter, streamPrefix_eq_intPrefix_div]
    refine and_congr_right fun _ => ?_
    have hw : ({w ∈ s | φ (intPrefix (x i) K) ≤ φ (intPrefix (x w) K)} : Finset ι) =
        {w ∈ s | intPrefix (x i) K ≤ intPrefix (x w) K} := by
      ext w
      simp [hmono.le_iff_le]
    rw [hw]
  set S : Finset ℤ := insert 0
    ((s.filter fun i => k ≤ #{w ∈ s | intPrefix (x i) K ≤ intPrefix (x w) K}).image
      fun i => intPrefix (x i) K)
  have hS_ne : S.Nonempty := insert_nonempty _ _
  have himg : insert (0 : ℝ)
      ((s.filter fun i => k ≤ #{w ∈ s | streamPrefix (x i) K ≤ streamPrefix (x w) K}).image
        fun i => streamPrefix (x i) K) = S.image φ := by
    rw [hfilt]
    dsimp [S]
    rw [image_insert, image_image]
    have h0 : φ 0 = 0 := by simp [φ]
    rw [h0]
    congr 2
    ext i
    exact streamPrefix_eq_intPrefix_div (x i) K
  change (insert (0 : ℝ)
      ((s.filter fun i => k ≤ #{w ∈ s | streamPrefix (x i) K ≤ streamPrefix (x w) K}).image
        fun i => streamPrefix (x i) K)).max' (insert_nonempty _ _) = φ (S.max' hS_ne)
  apply le_antisymm
  · refine max'_le _ _ _ fun r hr => ?_
    rw [himg] at hr
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hr
    exact hmono.monotone (le_max' S a ha)
  · have hmem : φ (S.max' hS_ne) ∈ insert (0 : ℝ)
        ((s.filter fun i => k ≤ #{w ∈ s | streamPrefix (x i) K ≤ streamPrefix (x w) K}).image
          fun i => streamPrefix (x i) K) := by
      rw [himg]
      exact mem_image_of_mem φ (max'_mem S hS_ne)
    exact le_max' _ _ hmem

private theorem abs_kthLargest_zero_sub_le {ι : Type*} (s : Finset ι) {f g : ι → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ i ∈ s, |f i - g i| ≤ ε) :
    |kthLargest 0 s f - kthLargest 0 s g| ≤ ε := by
  classical
  have hle_side (u v : ι → ℝ) (huv : ∀ i ∈ s, u i ≤ v i + ε) :
      kthLargest 0 s u ≤ kthLargest 0 s v + ε := by
    unfold kthLargest
    refine max'_le _ _ _ fun r hr => ?_
    rcases mem_insert.mp hr with rfl | hr
    · exact le_add_of_nonneg_of_le (le_max' _ _ (mem_insert_self _ _)) hε
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
      have his : i ∈ s := (mem_filter.mp hi).1
      have hvi : v i ≤ (insert 0 ((s.filter fun x => 0 ≤ #{w ∈ s | v x ≤ v w}).image v)).max'
          (insert_nonempty _ _) :=
        le_max' _ _ (mem_insert_of_mem (mem_image_of_mem v (mem_filter.mpr ⟨his, Nat.zero_le _⟩)))
      linarith [huv i his]
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · exact sub_le_iff_le_add'.mpr (hle_side f g fun i hi =>
      sub_le_iff_le_add'.mp (le_of_abs_le (h i hi)))
  · exact sub_le_iff_le_add'.mpr (hle_side g f fun i hi =>
      sub_le_iff_le_add'.mp (le_of_abs_le ((abs_sub_comm _ _).trans_le (h i hi))))

/-- **Zero-padded detector-rank approximation** (adapting [OpenAI2026LogSpace, Lemma 10.6] to the
zero-padded `Finset.kthLargest` of Sections 4.2 and 8.2): `zeroPaddedRankApprox k s x`
approximates `kthLargest k s (fun i => streamVal (x i))` within `< 2`. -/
theorem zeroPaddedRankApprox_isScaledApprox {ι : Type*} (k : ℕ) (s : Finset ι) {x : ι → ℕ → ℤ}
    (hx : ∀ i ∈ s, IsSignedStream (x i)) :
    IsScaledApprox (kthLargest k s fun i => streamVal (x i)) (zeroPaddedRankApprox k s x) := by
  intro t
  unfold zeroPaddedRankApprox
  have herr_pt : ∀ i ∈ s, |streamPrefix (x i) (t + 4) - streamVal (x i)| ≤ 6 / (2 : ℝ) ^ (t + 4) :=
    fun i hi => by
      rw [abs_sub_comm]
      exact abs_streamVal_sub_streamPrefix_le (hx i hi) (t + 4)
  have hstab : |kthLargest k s (fun i => streamPrefix (x i) (t + 4)) -
      kthLargest k s (fun i => streamVal (x i))| ≤ 6 / (2 : ℝ) ^ (t + 4) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact abs_kthLargest_zero_sub_le s (by positivity) herr_pt
    · exact abs_kthLargest_sub_kthLargest_le hk (by positivity) herr_pt
  refine abs_ediv_sub_lt_two_of_scaled _ (by decide : 0 < 16) ?_
    (abs_two_pow_mul_sub_le_of_prefix hstab)
  rw [kthLargest_streamPrefix_eq_div]
  have hpow : (2 : ℝ) ^ (t + 4) = 16 * (2 : ℝ) ^ t := by ring
  rw [hpow]
  push_cast
  field_simp

/-- Transition step of the 63-state absorbing `2 s - 3 u` comparator on `[-31, 31]`. -/
@[expose] def cmpBufferedStep (p δ : ℤ) : ℤ :=
  max (-31) (min 31 (2 * p + δ))

/-- Finite-state streaming comparator computing `2 * intPrefix s K - 3 * intPrefix u K` clamped
to `[-31, 31]`. -/
@[expose] def cmpBuffered (s u : ℕ → ℤ) : ℕ → ℤ
  | 0 => cmpBufferedStep 0 (2 * s 0 - 3 * u 0)
  | K + 1 => cmpBufferedStep (cmpBuffered s u K) (2 * s (K + 1) - 3 * u (K + 1))

/-- **Finite buffered test** [OpenAI2026LogSpace, Lemma 10.8]: accepts iff `2 * s̃ > 3 * ũ` at
fixed truncation place `K = M + R + 7`, independent of any outer numerical clock. -/
@[expose] def bufferedTest (M R : ℕ) (s u : ℕ → ℤ) : Bool :=
  decide (0 < cmpBuffered s u (M + R + 7))

theorem cmpBuffered_mem_Icc (s u : ℕ → ℤ) (K : ℕ) :
    cmpBuffered s u K ∈ Set.Icc (-31 : ℤ) 31 := by
  cases K <;> exact ⟨le_max_left _ _, max_le (by decide) (min_le_left _ _)⟩

theorem cmpBuffered_eq_clamp {s u : ℕ → ℤ} (hs : IsSignedStream s) (hu : IsSignedStream u)
    (K : ℕ) :
    cmpBuffered s u K = max (-31) (min 31 (2 * intPrefix s K - 3 * intPrefix u K)) := by
  induction K with
  | zero =>
    simp [cmpBuffered, cmpBufferedStep, intPrefix_zero]
  | succ K ih =>
    rw [cmpBuffered, ih, intPrefix_succ, intPrefix_succ]
    unfold cmpBufferedStep
    have hsK := isSignedDigit_iff_le.mp (hs (K + 1))
    have huK := isSignedDigit_iff_le.mp (hu (K + 1))
    set D := 2 * intPrefix s K - 3 * intPrefix u K
    set δ := 2 * s (K + 1) - 3 * u (K + 1)
    have hdiff : 2 * (2 * intPrefix s K + s (K + 1)) - 3 * (2 * intPrefix u K + u (K + 1)) =
        2 * D + δ := by ring
    rw [hdiff]
    omega

theorem cmpBuffered_pos_iff {s u : ℕ → ℤ} (hs : IsSignedStream s) (hu : IsSignedStream u)
    (K : ℕ) :
    0 < cmpBuffered s u K ↔ 3 * streamPrefix u K < 2 * streamPrefix s K := by
  rw [cmpBuffered_eq_clamp hs hu K, streamPrefix_eq_intPrefix_div, streamPrefix_eq_intPrefix_div]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hdiv : 3 * ((intPrefix u K : ℝ) / (2 : ℝ) ^ K) <
      2 * ((intPrefix s K : ℝ) / (2 : ℝ) ^ K) ↔
      3 * intPrefix u K < 2 * intPrefix s K := by
    rw [← mul_div_assoc, ← mul_div_assoc, div_lt_div_iff_of_pos_right hpos]
    exact_mod_cast Iff.rfl
  rw [hdiv]
  omega

/-- Truncation error of the buffered test at place `K = M + R + 7`, at scale `2 ^ M`: the
scaled prefix is within the slack `(3 / 64) / 2 ^ R` of the scaled value. -/
private theorem abs_two_pow_mul_streamPrefix_sub_le {M R : ℕ} {x : ℕ → ℤ}
    (hx : IsSignedStream x) :
    |(2 : ℝ) ^ M * streamPrefix x (M + R + 7) - (2 : ℝ) ^ M * streamVal x| ≤
      (3 / 64) / (2 : ℝ) ^ R := by
  have h := abs_streamVal_sub_streamPrefix_le hx (M + R + 7)
  rw [abs_sub_comm] at h
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)]
  calc (2 : ℝ) ^ M * |streamPrefix x (M + R + 7) - streamVal x|
      ≤ (2 : ℝ) ^ M * (6 / (2 : ℝ) ^ (M + R + 7)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (3 / 64) / (2 : ℝ) ^ R := by
        have hp : (2 : ℝ) ^ (M + R + 7) = 128 * ((2 : ℝ) ^ M * (2 : ℝ) ^ R) := by ring
        rw [hp]
        field_simp
        ring

/-- Five times the buffered-test slack `(3 / 64) / 2 ^ R` is below any `ρ ≥ 1 / 2 ^ R`. -/
private theorem five_mul_slack_lt {R : ℕ} {ρ : ℝ} (hρ : 1 / (2 : ℝ) ^ R ≤ ρ) :
    5 * ((3 / 64) / (2 : ℝ) ^ R) < ρ := by
  have hρ0 : (0 : ℝ) < 1 / (2 : ℝ) ^ R := by positivity
  have h : 5 * ((3 / 64) / (2 : ℝ) ^ R) = (15 / 64) * (1 / (2 : ℝ) ^ R) := by ring
  linarith

/-- **Lemma 10.8 (completeness of buffered test)** [OpenAI2026LogSpace, Lemma 10.8]: if `sVal` and
`uVal` have normalized streams `s, u` at scale `2 ^ M`, `uVal ≥ ρ ≥ 1 / 2 ^ R`, and
`2 * uVal < sVal`, then `bufferedTest M R s u = true`. -/
theorem bufferedTest_eq_true_of_two_mul_lt {M R : ℕ} {s u : ℕ → ℤ}
    (hs : IsSignedStream s) (hu : IsSignedStream u)
    {sVal uVal ρ : ℝ} (hsVal : sVal = (2 : ℝ) ^ M * streamVal s)
    (huVal : uVal = (2 : ℝ) ^ M * streamVal u)
    (hρ : 1 / (2 : ℝ) ^ R ≤ ρ) (huρ : ρ ≤ uVal) (hlt : 2 * uVal < sVal) :
    bufferedTest M R s u = true := by
  unfold bufferedTest
  rw [decide_eq_true_eq, cmpBuffered_pos_iff hs hu]
  have hs_err := abs_two_pow_mul_streamPrefix_sub_le (M := M) (R := R) hs
  have hu_err := abs_two_pow_mul_streamPrefix_sub_le (M := M) (R := R) hu
  rw [← hsVal] at hs_err
  rw [← huVal] at hu_err
  have hscaled : (2 : ℝ) ^ M * (3 * streamPrefix u (M + R + 7)) <
      (2 : ℝ) ^ M * (2 * streamPrefix s (M + R + 7)) := by
    linarith [five_mul_slack_lt hρ, neg_le_of_abs_le hs_err, le_of_abs_le hu_err]
  exact lt_of_mul_lt_mul_left hscaled (by positivity)

/-- **Lemma 10.8 (soundness of buffered test)** [OpenAI2026LogSpace, Lemma 10.8]: under the same
scaling hypotheses, if `sVal ≤ uVal`, then `bufferedTest M R s u = false`. -/
theorem bufferedTest_eq_false_of_le {M R : ℕ} {s u : ℕ → ℤ}
    (hs : IsSignedStream s) (hu : IsSignedStream u)
    {sVal uVal ρ : ℝ} (hsVal : sVal = (2 : ℝ) ^ M * streamVal s)
    (huVal : uVal = (2 : ℝ) ^ M * streamVal u)
    (hρ : 1 / (2 : ℝ) ^ R ≤ ρ) (huρ : ρ ≤ uVal) (hle : sVal ≤ uVal) :
    bufferedTest M R s u = false := by
  unfold bufferedTest
  rw [decide_eq_false_iff_not]
  intro hlt_raw
  have hlt := (cmpBuffered_pos_iff hs hu (M + R + 7)).mp hlt_raw
  have hs_err := abs_two_pow_mul_streamPrefix_sub_le (M := M) (R := R) hs
  have hu_err := abs_two_pow_mul_streamPrefix_sub_le (M := M) (R := R) hu
  rw [← hsVal] at hs_err
  rw [← huVal] at hu_err
  have hmul_lt := mul_lt_mul_of_pos_left hlt (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)
  linarith [five_mul_slack_lt hρ, le_of_abs_le hs_err, neg_le_of_abs_le hu_err]

end OrderStatisticsAndBufferedTests

end Cslib.SignedDigitStream
