/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Avizienis signed-digit streams and approximation residues

This module formalizes the redundant radix-2 signed-digit stream representation over the alphabet
`{-6, ..., 6}` and the reduction of exact stream generation to mod-`2^q` integer approximation
residues from [OpenAI2026LogSpace, Section 10.1, Lemma 10.1].

A sequence `x : ℕ → ℤ` with `|x j| ≤ 6` represents the real number
`streamVal x = ∑' j, (x j : ℝ) / 2 ^ j`, with finite `K`-place truncation
`streamPrefix x K = ∑ j ∈ range (K + 1), (x j : ℝ) / 2 ^ j` satisfying
`|streamVal x - streamPrefix x K| ≤ 6 / 2 ^ K`.

Conversely, if `|z| ≤ 1` and deterministic integers `N : ℕ → ℤ` satisfy the scaled approximation
bound `|N t - 2 ^ t * z| < 2` for every `t : ℕ`, then the difference digits `diffDigit N 0 = N 0`
and `diffDigit N (t + 1) = N (t + 1) - 2 * N t` belong to `{-6, ..., 6}`, telescope to
`N T / 2 ^ T`, sum to `z`, and can be decoded uniquely from `N t % 2 ^ q` and `N (t - 1) % 2 ^ q`
for any `q ≥ 4`. Moreover, signed floor shifts preserve residues: `(a / 2 ^ s) % 2 ^ q` equals
`(a % 2 ^ (q + s)) / 2 ^ s` for every signed integer `a : ℤ`.

## Main definitions

* `Cslib.SignedDigitStream.IsSignedDigit`, `Cslib.SignedDigitStream.IsSignedStream`: the redundant
  digit alphabet `{-6, ..., 6}` and valid digit streams.
* `Cslib.SignedDigitStream.intPrefix`, `Cslib.SignedDigitStream.streamPrefix`,
  `Cslib.SignedDigitStream.streamVal`: scaled integer prefixes, real finite prefixes, and infinite
  real stream values.
* `Cslib.SignedDigitStream.suffixStream`: zeroed-prefix remainder stream `x - x^{[K]}`.
* `Cslib.SignedDigitStream.IsScaledApprox`, `Cslib.SignedDigitStream.diffDigit`: scaled integer
  approximations `|N t - 2 ^ t * z| < 2` and telescoping difference digits.
* `Cslib.SignedDigitStream.centeredResidue`, `Cslib.SignedDigitStream.decodeDiffResidue`: unique
  signed-digit recovery from mod-`2^q` residues (`q ≥ 4`).

## Main results

* `Cslib.SignedDigitStream.abs_streamVal_sub_streamPrefix_le`: tail error bound `6 / 2 ^ K`.
* `Cslib.SignedDigitStream.diffDigit_isSignedStream`,
  `Cslib.SignedDigitStream.hasSum_diffDigit`, `Cslib.SignedDigitStream.streamVal_diffDigit`:
  Lemma 10.1 exact stream synthesis from approximations.
* `Cslib.SignedDigitStream.decodeDiffResidue_eq_diffDigit`: Lemma 10.1 mod-`2^q` residue decoding.
* `Cslib.SignedDigitStream.ediv_two_pow_emod_eq`: signed floor-shift congruence modulo `2^q`.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 10.1, Equations (10.1)--(10.4), (10.12), and Lemma 10.1 (23 September 2026,
  revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.SignedDigitStream

open Finset

/-- A redundant radix-2 signed digit in the alphabet `{-6, ..., 6}`. -/
@[expose] def IsSignedDigit (d : ℤ) : Prop := |d| ≤ 6

/-- A stream of redundant radix-2 signed digits in `{-6, ..., 6}`. -/
@[expose] def IsSignedStream (x : ℕ → ℤ) : Prop := ∀ j, IsSignedDigit (x j)

/-- The scaled integer prefix `∑_{j = 0}^K x_j 2^{K - j}` of a digit stream. -/
@[expose] def intPrefix (x : ℕ → ℤ) (K : ℕ) : ℤ :=
  ∑ j ∈ range (K + 1), x j * (2 : ℤ) ^ (K - j)

/-- The real `K`-place prefix `x^{[K]} = ∑_{j = 0}^K x_j 2^{-j}` of a digit stream. -/
@[expose] noncomputable def streamPrefix (x : ℕ → ℤ) (K : ℕ) : ℝ :=
  ∑ j ∈ range (K + 1), (x j : ℝ) / (2 : ℝ) ^ j

/-- The real number `∑_{j = 0}^∞ x_j 2^{-j}` represented by a digit stream. -/
@[expose] noncomputable def streamVal (x : ℕ → ℤ) : ℝ :=
  ∑' j : ℕ, (x j : ℝ) / (2 : ℝ) ^ j

/-- The remainder stream with zeros through place `K` and `x j` for `j > K`. -/
@[expose] def suffixStream (x : ℕ → ℤ) (K : ℕ) (j : ℕ) : ℤ :=
  if j ≤ K then 0 else x j

/-- Deterministic integer approximations `N t` to `2 ^ t * z` within strict error `2`
[OpenAI2026LogSpace, (10.3)]. -/
@[expose] def IsScaledApprox (z : ℝ) (N : ℕ → ℤ) : Prop :=
  ∀ t : ℕ, |(N t : ℝ) - (2 : ℝ) ^ t * z| < 2

/-- Telescoping difference digits `z_0 = N_0` and `z_{t+1} = N_{t+1} - 2 N_t`
[OpenAI2026LogSpace, (10.4)]. -/
@[expose] def diffDigit (N : ℕ → ℤ) : ℕ → ℤ
  | 0 => N 0
  | t + 1 => N (t + 1) - 2 * N t

/-- Centered representative of `r` modulo `2 ^ q` in `(-2 ^ (q - 1), 2 ^ (q - 1)]`. -/
@[expose] def centeredResidue (q : ℕ) (r : ℤ) : ℤ :=
  let m := r % (2 : ℤ) ^ q
  if m ≤ (2 : ℤ) ^ (q - 1) then m else m - (2 : ℤ) ^ q

/-- Decode the place-`t` difference digit solely from the mod-`2^q` residues `rCurr = N_t mod 2^q`
and `rPrev = N_{t-1} mod 2^q` (at `t = 0`, `rPrev` is unused). -/
@[expose] def decodeDiffResidue (q : ℕ) (rCurr rPrev : ℤ) : ℕ → ℤ
  | 0 => centeredResidue q rCurr
  | _ + 1 => centeredResidue q (rCurr - 2 * rPrev)

section DigitBasics

theorem isSignedDigit_iff_le {d : ℤ} : IsSignedDigit d ↔ -6 ≤ d ∧ d ≤ 6 :=
  abs_le

theorem isSignedDigit_iff_mem_Icc {d : ℤ} : IsSignedDigit d ↔ d ∈ Set.Icc (-6 : ℤ) 6 :=
  abs_le

theorem isSignedDigit_zero : IsSignedDigit 0 := by
  simp [IsSignedDigit]

theorem IsSignedDigit.neg {d : ℤ} (hd : IsSignedDigit d) : IsSignedDigit (-d) := by
  simpa only [IsSignedDigit, abs_neg] using hd

theorem isSignedStream_zero : IsSignedStream (fun _ => 0) :=
  fun _ => isSignedDigit_zero

theorem IsSignedStream.neg {x : ℕ → ℤ} (hx : IsSignedStream x) :
    IsSignedStream (fun j => -x j) :=
  fun j => (hx j).neg

theorem IsSignedStream.abs_cast_le {x : ℕ → ℤ} (hx : IsSignedStream x) (j : ℕ) :
    |(x j : ℝ)| ≤ 6 := by
  exact_mod_cast hx j

end DigitBasics

section PrefixesAndConvergence

@[simp]
theorem intPrefix_zero (x : ℕ → ℤ) : intPrefix x 0 = x 0 := by
  simp [intPrefix]

theorem intPrefix_succ (x : ℕ → ℤ) (K : ℕ) :
    intPrefix x (K + 1) = 2 * intPrefix x K + x (K + 1) := by
  unfold intPrefix
  rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_sum]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hjle : j ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hsub : K + 1 - j = (K - j) + 1 := by omega
  rw [hsub, pow_succ]
  ring

theorem abs_intPrefix_le {x : ℕ → ℤ} (hx : IsSignedStream x) (K : ℕ) :
    |intPrefix x K| ≤ 12 * (2 : ℤ) ^ K - 6 := by
  induction K with
  | zero =>
    have h0 : |x 0| ≤ 6 := hx 0
    simp only [intPrefix_zero, pow_zero, mul_one]
    omega
  | succ K ih =>
    rw [intPrefix_succ]
    have hxK : |x (K + 1)| ≤ 6 := hx (K + 1)
    have hpow : (2 : ℤ) ^ (K + 1) = 2 * (2 : ℤ) ^ K := by ring
    have htri : |2 * intPrefix x K + x (K + 1)| ≤ 2 * |intPrefix x K| + |x (K + 1)| := by
      calc |2 * intPrefix x K + x (K + 1)|
          ≤ |2 * intPrefix x K| + |x (K + 1)| := abs_add_le _ _
        _ = 2 * |intPrefix x K| + |x (K + 1)| := by rw [abs_mul]; norm_num
    omega

@[simp]
theorem streamPrefix_zero (x : ℕ → ℤ) : streamPrefix x 0 = (x 0 : ℝ) := by
  simp [streamPrefix]

theorem streamPrefix_succ (x : ℕ → ℤ) (K : ℕ) :
    streamPrefix x (K + 1) = streamPrefix x K + (x (K + 1) : ℝ) / (2 : ℝ) ^ (K + 1) := by
  unfold streamPrefix
  exact sum_range_succ _ (K + 1)

theorem streamPrefix_eq_intPrefix_div (x : ℕ → ℤ) (K : ℕ) :
    streamPrefix x K = (intPrefix x K : ℝ) / (2 : ℝ) ^ K := by
  induction K with
  | zero =>
    simp [streamPrefix_zero, intPrefix_zero]
  | succ K ih =>
    rw [streamPrefix_succ, ih, intPrefix_succ]
    push_cast
    field_simp
    ring

theorem abs_streamPrefix_le {x : ℕ → ℤ} (hx : IsSignedStream x) (K : ℕ) :
    |streamPrefix x K| ≤ 12 - 6 / (2 : ℝ) ^ K := by
  rw [streamPrefix_eq_intPrefix_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ K)]
  have hint : |(intPrefix x K : ℝ)| ≤ 12 * (2 : ℝ) ^ K - 6 := by
    exact_mod_cast abs_intPrefix_le hx K
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ K)]
  calc |(intPrefix x K : ℝ)|
      ≤ 12 * (2 : ℝ) ^ K - 6 := hint
    _ = (12 - 6 / (2 : ℝ) ^ K) * (2 : ℝ) ^ K := by field_simp

theorem IsSignedStream.summable {x : ℕ → ℤ} (hx : IsSignedStream x) :
    Summable (fun j : ℕ => (x j : ℝ) / (2 : ℝ) ^ j) := by
  refine Summable.of_norm_bounded (summable_geometric_two.mul_left 6) fun j => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ j),
    one_div_pow, mul_one_div]
  exact div_le_div_of_nonneg_right (hx.abs_cast_le j) (by positivity)

/-- **Tail truncation bound** [OpenAI2026LogSpace, (10.2)]: truncating a signed-digit stream after
place `K` incurs error at most `6 / 2 ^ K`. -/
theorem abs_streamVal_sub_streamPrefix_le {x : ℕ → ℤ} (hx : IsSignedStream x) (K : ℕ) :
    |streamVal x - streamPrefix x K| ≤ 6 / (2 : ℝ) ^ K := by
  have hsplit := hx.summable.sum_add_tsum_nat_add (K + 1)
  have hsub : streamVal x - streamPrefix x K =
      ∑' m : ℕ, (x (m + (K + 1)) : ℝ) / (2 : ℝ) ^ (m + (K + 1)) := by
    unfold streamVal streamPrefix
    linarith
  rw [hsub, ← Real.norm_eq_abs]
  have hgeom : HasSum (fun m : ℕ => (6 / (2 : ℝ) ^ (K + 1)) * (1 / 2 : ℝ) ^ m)
      (6 / (2 : ℝ) ^ K) := by
    convert hasSum_geometric_two.mul_left (6 / (2 : ℝ) ^ (K + 1)) using 1
    field_simp
    ring
  refine tsum_of_norm_bounded hgeom fun m => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (m + (K + 1)))]
  have hxm : |(x (m + (K + 1)) : ℝ)| ≤ 6 := hx.abs_cast_le (m + (K + 1))
  have hpow : (2 : ℝ) ^ (m + (K + 1)) = (2 : ℝ) ^ (K + 1) * (2 : ℝ) ^ m := by ring
  rw [hpow, one_div_pow]
  calc |(x (m + (K + 1)) : ℝ)| / ((2 : ℝ) ^ (K + 1) * (2 : ℝ) ^ m)
      ≤ 6 / ((2 : ℝ) ^ (K + 1) * (2 : ℝ) ^ m) := by gcongr
    _ = 6 / (2 : ℝ) ^ (K + 1) * (1 / (2 : ℝ) ^ m) := by ring

theorem abs_streamVal_le_twelve {x : ℕ → ℤ} (hx : IsSignedStream x) :
    |streamVal x| ≤ 12 := by
  have h0 := abs_streamVal_sub_streamPrefix_le hx 0
  have hp0 : |streamPrefix x 0| ≤ 6 := by
    simpa only [streamPrefix_zero] using hx.abs_cast_le 0
  have hpow : (6 : ℝ) / (2 : ℝ) ^ (0 : ℕ) = 6 := by norm_num
  linarith [abs_sub_abs_le_abs_sub (streamVal x) (streamPrefix x 0)]

theorem suffixStream_isSignedStream {x : ℕ → ℤ} (hx : IsSignedStream x) (K : ℕ) :
    IsSignedStream (suffixStream x K) := by
  intro j
  unfold suffixStream
  split_ifs
  · exact isSignedDigit_zero
  · exact hx j

theorem streamPrefix_suffixStream_le (x : ℕ → ℤ) {K M : ℕ} (hM : M ≤ K) :
    streamPrefix (suffixStream x K) M = 0 := by
  unfold streamPrefix suffixStream
  refine sum_eq_zero fun j hj => ?_
  have hjK : j ≤ K := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans hM
  simp [hjK]

theorem streamVal_suffixStream {x : ℕ → ℤ} (hx : IsSignedStream x) (K : ℕ) :
    streamVal (suffixStream x K) = streamVal x - streamPrefix x K := by
  have hsx := hx.summable.sum_add_tsum_nat_add (K + 1)
  have hss := (suffixStream_isSignedStream hx K).summable.sum_add_tsum_nat_add (K + 1)
  have hpre0 : ∑ j ∈ range (K + 1), (suffixStream x K j : ℝ) / (2 : ℝ) ^ j = 0 :=
    streamPrefix_suffixStream_le x le_rfl
  have htail : (fun m : ℕ => (suffixStream x K (m + (K + 1)) : ℝ) / (2 : ℝ) ^ (m + (K + 1))) =
      fun m : ℕ => (x (m + (K + 1)) : ℝ) / (2 : ℝ) ^ (m + (K + 1)) := by
    ext m
    have hnot : ¬ m + (K + 1) ≤ K := by omega
    simp [suffixStream, hnot]
  rw [hpre0, zero_add, htail] at hss
  unfold streamVal streamPrefix
  linarith

end PrefixesAndConvergence

section ResidueStream

theorem abs_diffDigit_zero_le {z : ℝ} {N : ℕ → ℤ} (hz : |z| ≤ 1) (hN : IsScaledApprox z N) :
    |diffDigit N 0| ≤ 2 := by
  have h0 : |(N 0 : ℝ) - z| < 2 := by simpa only [pow_zero, one_mul] using hN 0
  have habs : |(N 0 : ℝ)| < 3 := by
    linarith [abs_sub_abs_le_abs_sub (N 0 : ℝ) z]
  have hint : |N 0| < 3 := by exact_mod_cast habs
  simp only [diffDigit]
  omega

theorem abs_diffDigit_succ_le {z : ℝ} {N : ℕ → ℤ} (hN : IsScaledApprox z N) (t : ℕ) :
    |diffDigit N (t + 1)| ≤ 5 := by
  have ht : |(N t : ℝ) - (2 : ℝ) ^ t * z| < 2 := hN t
  have ht1 : |(N (t + 1) : ℝ) - (2 : ℝ) ^ (t + 1) * z| < 2 := hN (t + 1)
  have hdecomp : (diffDigit N (t + 1) : ℝ) =
      ((N (t + 1) : ℝ) - (2 : ℝ) ^ (t + 1) * z) - 2 * ((N t : ℝ) - (2 : ℝ) ^ t * z) := by
    unfold diffDigit
    push_cast
    ring
  have habs : |(diffDigit N (t + 1) : ℝ)| < 6 := by
    rw [hdecomp]
    have htri := abs_sub ((N (t + 1) : ℝ) - (2 : ℝ) ^ (t + 1) * z)
      (2 * ((N t : ℝ) - (2 : ℝ) ^ t * z))
    have hmul : |2 * ((N t : ℝ) - (2 : ℝ) ^ t * z)| = 2 * |(N t : ℝ) - (2 : ℝ) ^ t * z| := by
      rw [abs_mul]
      norm_num
    linarith
  have hint : |diffDigit N (t + 1)| < 6 := by exact_mod_cast habs
  omega

/-- **Lemma 10.1 (digit range)** [OpenAI2026LogSpace, Lemma 10.1]: difference digits of any scaled
approximation to `z ∈ [-1, 1]` lie in `{-6, ..., 6}` (indeed `|z_0| ≤ 2` and `|z_{t+1}| ≤ 5`). -/
theorem diffDigit_isSignedStream {z : ℝ} {N : ℕ → ℤ} (hz : |z| ≤ 1) (hN : IsScaledApprox z N) :
    IsSignedStream (diffDigit N)
  | 0 => (abs_diffDigit_zero_le hz hN).trans (by decide)
  | t + 1 => (abs_diffDigit_succ_le hN t).trans (by decide)

theorem intPrefix_diffDigit (N : ℕ → ℤ) (T : ℕ) :
    intPrefix (diffDigit N) T = N T := by
  induction T with
  | zero =>
    simp [intPrefix_zero, diffDigit]
  | succ T ih =>
    rw [intPrefix_succ, ih, diffDigit]
    ring

theorem streamPrefix_diffDigit (N : ℕ → ℤ) (T : ℕ) :
    streamPrefix (diffDigit N) T = (N T : ℝ) / (2 : ℝ) ^ T := by
  rw [streamPrefix_eq_intPrefix_div, intPrefix_diffDigit]

theorem abs_streamPrefix_diffDigit_sub_lt {z : ℝ} {N : ℕ → ℤ}
    (hN : IsScaledApprox z N) (T : ℕ) :
    |streamPrefix (diffDigit N) T - z| < 2 / (2 : ℝ) ^ T := by
  rw [streamPrefix_diffDigit]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have heq : (N T : ℝ) / (2 : ℝ) ^ T - z = ((N T : ℝ) - (2 : ℝ) ^ T * z) / (2 : ℝ) ^ T := by
    field_simp
  rw [heq, abs_div, abs_of_pos hpos]
  exact div_lt_div_of_pos_right (hN T) hpos

/-- **Lemma 10.1 (exact representation)** [OpenAI2026LogSpace, Lemma 10.1]: the difference digits
of `N` sum to `z`. -/
theorem streamVal_diffDigit {z : ℝ} {N : ℕ → ℤ} (hz : |z| ≤ 1) (hN : IsScaledApprox z N) :
    streamVal (diffDigit N) = z := by
  have hstream := diffDigit_isSignedStream hz hN
  by_contra hne
  have hgap : 0 < |streamVal (diffDigit N) - z| := abs_sub_pos.mpr hne
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one (div_pos hgap (by norm_num : (0 : ℝ) < 8))
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h1 := abs_streamVal_sub_streamPrefix_le hstream T
  have h2 := abs_streamPrefix_diffDigit_sub_lt hN T
  have htri : |streamVal (diffDigit N) - z| < 8 / (2 : ℝ) ^ T := by
    have hsub := abs_sub_le (streamVal (diffDigit N)) (streamPrefix (diffDigit N) T) z
    have hsum : (6 : ℝ) / (2 : ℝ) ^ T + 2 / (2 : ℝ) ^ T = 8 / (2 : ℝ) ^ T := by ring
    linarith
  have hpow : (1 / 2 : ℝ) ^ T = 1 / (2 : ℝ) ^ T := one_div_pow 2 T
  rw [hpow] at hT
  have hmul := mul_lt_mul_of_pos_left hT (by norm_num : (0 : ℝ) < 8)
  have hrw : (8 : ℝ) * (1 / (2 : ℝ) ^ T) = 8 / (2 : ℝ) ^ T := by ring
  have hcancel : (8 : ℝ) * (|streamVal (diffDigit N) - z| / 8) =
      |streamVal (diffDigit N) - z| := by ring
  linarith

theorem hasSum_diffDigit {z : ℝ} {N : ℕ → ℤ} (hz : |z| ≤ 1) (hN : IsScaledApprox z N) :
    HasSum (fun j : ℕ => (diffDigit N j : ℝ) / (2 : ℝ) ^ j) z := by
  rw [← streamVal_diffDigit hz hN]
  exact (diffDigit_isSignedStream hz hN).summable.hasSum

@[simp]
theorem centeredResidue_emod (q : ℕ) (r : ℤ) :
    centeredResidue q (r % (2 : ℤ) ^ q) = centeredResidue q r := by
  unfold centeredResidue
  simp only [Int.emod_emod]

theorem centeredResidue_eq_self {q : ℕ} (hq : 4 ≤ q) {d : ℤ} (hd : IsSignedDigit d) :
    centeredResidue q d = d := by
  unfold centeredResidue
  have hq1 : (8 : ℤ) ≤ (2 : ℤ) ^ (q - 1) := by
    have hle : 3 ≤ q - 1 := by omega
    calc (8 : ℤ) = (2 : ℤ) ^ 3 := by decide
      _ ≤ (2 : ℤ) ^ (q - 1) := pow_le_pow_right₀ (by decide) hle
  have hpow : (2 : ℤ) ^ q = 2 * (2 : ℤ) ^ (q - 1) := by
    have hqeq : q = (q - 1) + 1 := by omega
    conv_lhs => rw [hqeq, pow_succ]
    ring
  have hd_bounds := isSignedDigit_iff_le.mp hd
  by_cases hd0 : 0 ≤ d
  · have hmod : d % (2 : ℤ) ^ q = d := Int.emod_eq_of_lt hd0 (by omega)
    have hle : d ≤ (2 : ℤ) ^ (q - 1) := by omega
    simp [hmod, hle]
  · have hadd0 : 0 ≤ d + (2 : ℤ) ^ q := by omega
    have haddlt : d + (2 : ℤ) ^ q < (2 : ℤ) ^ q := by omega
    have hmod : d % (2 : ℤ) ^ q = d + (2 : ℤ) ^ q := by
      have hcongr : (d + (2 : ℤ) ^ q) % (2 : ℤ) ^ q = d % (2 : ℤ) ^ q :=
        Int.add_emod_right d ((2 : ℤ) ^ q)
      rw [← hcongr, Int.emod_eq_of_lt hadd0 haddlt]
    have hnotle : ¬ d + (2 : ℤ) ^ q ≤ (2 : ℤ) ^ (q - 1) := by omega
    simp [hmod, hnotle]

/-- **Lemma 10.1 (residue decoding)** [OpenAI2026LogSpace, Lemma 10.1]: for `q ≥ 4`, the place-`t`
difference digit is uniquely determined by `N t % 2 ^ q` and `N (t - 1) % 2 ^ q`. -/
theorem decodeDiffResidue_eq_diffDigit {q : ℕ} (hq : 4 ≤ q) {z : ℝ} {N : ℕ → ℤ}
    (hz : |z| ≤ 1) (hN : IsScaledApprox z N) (t : ℕ) :
    decodeDiffResidue q (N t % (2 : ℤ) ^ q) (N (t - 1) % (2 : ℤ) ^ q) t = diffDigit N t := by
  have hdig : IsSignedDigit (diffDigit N t) := diffDigit_isSignedStream hz hN t
  cases t with
  | zero =>
    unfold decodeDiffResidue
    rw [centeredResidue_emod]
    exact centeredResidue_eq_self hq hdig
  | succ t =>
    simp only [decodeDiffResidue, Nat.add_sub_cancel]
    have hmod : (N (t + 1) % (2 : ℤ) ^ q - 2 * (N t % (2 : ℤ) ^ q)) % (2 : ℤ) ^ q =
        diffDigit N (t + 1) % (2 : ℤ) ^ q := by
      unfold diffDigit
      conv_rhs => rw [Int.sub_emod, Int.mul_emod]
      rw [Int.sub_emod, Int.emod_emod, Int.mul_emod (2 : ℤ) (N t % (2 : ℤ) ^ q), Int.emod_emod]
    rw [← centeredResidue_emod, hmod, centeredResidue_emod]
    exact centeredResidue_eq_self hq hdig

/-- **Signed floor-shift residue identity** [OpenAI2026LogSpace, (10.12)]: discarding the low `s`
bits of the canonical `(q + s)`-bit Euclidean residue computes the mod-`2^q` residue of the signed
floor quotient `a / 2 ^ s` for every signed integer `a : ℤ`. -/
theorem ediv_two_pow_emod_eq (a : ℤ) (q s : ℕ) :
    (a / (2 : ℤ) ^ s) % (2 : ℤ) ^ q = (a % (2 : ℤ) ^ (q + s)) / (2 : ℤ) ^ s := by
  have hs_pos : (0 : ℤ) < (2 : ℤ) ^ s := by positivity
  have hq_pos : (0 : ℤ) < (2 : ℤ) ^ q := by positivity
  have hqs_pos : (0 : ℤ) < (2 : ℤ) ^ (q + s) := by positivity
  set M := (2 : ℤ) ^ (q + s)
  set r := a % M
  have hr0 : 0 ≤ r := Int.emod_nonneg a hqs_pos.ne'
  have hrlt : r < (2 : ℤ) ^ s * (2 : ℤ) ^ q := by
    have hpow : M = (2 : ℤ) ^ s * (2 : ℤ) ^ q := by
      dsimp [M]
      rw [pow_add]
      ring
    rw [← hpow]
    exact Int.emod_lt_of_pos a hqs_pos
  have ha : a = (2 : ℤ) ^ s * ((2 : ℤ) ^ q * (a / M)) + r := by
    have hdiv : M * (a / M) + r = a := by
      dsimp [r]
      linarith [Int.emod_def a M]
    have hpow : M = (2 : ℤ) ^ s * (2 : ℤ) ^ q := by
      dsimp [M]
      rw [pow_add]
      ring
    calc a = M * (a / M) + r := hdiv.symm
      _ = (2 : ℤ) ^ s * (2 : ℤ) ^ q * (a / M) + r := by rw [hpow]
      _ = (2 : ℤ) ^ s * ((2 : ℤ) ^ q * (a / M)) + r := by ring
  have hediv : a / (2 : ℤ) ^ s = (2 : ℤ) ^ q * (a / M) + r / (2 : ℤ) ^ s := by
    conv_lhs => rw [ha, add_comm]
    rw [Int.add_mul_ediv_left _ _ hs_pos.ne', add_comm]
  have hdiv0 : 0 ≤ r / (2 : ℤ) ^ s := Int.ediv_nonneg hr0 hs_pos.le
  have hdivlt : r / (2 : ℤ) ^ s < (2 : ℤ) ^ q :=
    Int.ediv_lt_of_lt_mul hs_pos (by linarith)
  rw [hediv, add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hdiv0 hdivlt]

end ResidueStream

end Cslib.SignedDigitStream
