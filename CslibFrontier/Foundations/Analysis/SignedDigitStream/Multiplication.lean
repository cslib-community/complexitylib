/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.SignedDigitStream.Elementary
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Minimum-index dyadic band multiplication of signed-digit streams

This module formalizes the minimum-index dyadic band multiplication algorithm of
[OpenAI2026LogSpace, Section 10.3, Lemma 10.4].

Grouping cross-terms `x_i y_j 2^{-(i+j)}` by `min i j` into a zero band (`min i j = 0`) and
positive dyadic bands `2 ^ k ≤ min i j < 2 ^ (k + 1)` with band-specific truncation margin
`bandMargin k = 16 + bandStart k / 4` achieves three properties simultaneously:

1. **Scaled accuracy `< 2`** (`mulApprox_isScaledApprox`): folding the retained band sums from
   `maxBand t` down to `0` by signed floor shifts approximates `2 ^ t * (streamVal x * streamVal y)`
   within `< 2`.
2. **Diagonal residue locality** (`mulResidue_eq_mulApprox_emod`): modulo `2 ^ q`, `mulApprox x y t`
   depends in band `k` only on diagonals `t - q < i + j ≤ t + bandMargin k`, propagated downward by
   exact signed floor shifts of residues (`ediv_two_pow_emod_eq`).
3. **Clock-drop latency payment** (`three_mul_bandStart_le_four_mul_drop`): for any retained pair
   `(i, j)` in a positive band `k + 1` (`D = 2 ^ k`), both indices satisfy
   `4 * j + 3 * D ≤ 4 * (t + 16)`, so `D ≤ (4 / 3) * (t - j + 16)` pays for the band circuit depth
   out of the clock drop `t - j`.

## Main definitions

* `Cslib.SignedDigitStream.mulBaseMargin`, `Cslib.SignedDigitStream.bandStart`,
  `Cslib.SignedDigitStream.bandEnd`, `Cslib.SignedDigitStream.bandIdx`,
  `Cslib.SignedDigitStream.bandMargin`, `Cslib.SignedDigitStream.maxBand`: dyadic band geometry.
* `Cslib.SignedDigitStream.bandPairs`, `Cslib.SignedDigitStream.bandSum`,
  `Cslib.SignedDigitStream.bandFold`, `Cslib.SignedDigitStream.mulApprox`: exact integer band
  recursion and scaled product approximation.
* `Cslib.SignedDigitStream.bandWindowPairs`, `Cslib.SignedDigitStream.bandWindowSum`,
  `Cslib.SignedDigitStream.bandFoldMod`, `Cslib.SignedDigitStream.mulResidue`: windowed modular
  product residue computation.

## Main results

* `Cslib.SignedDigitStream.mulApprox_isScaledApprox`: `< 2` scaled error bound for `x * y`.
* `Cslib.SignedDigitStream.mulResidue_eq_mulApprox_emod`: equivalence of the windowed residue fold
  with `mulApprox x y t % 2 ^ q`.
* `Cslib.SignedDigitStream.three_mul_bandStart_le_four_mul_drop`,
  `Cslib.SignedDigitStream.index_le_clock_add_baseMargin`: clock-drop latency inequalities.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 10.3, Equations (10.6)--(10.12), and Lemma 10.4 (23 September 2026, revision `7ef5c0cc`,
  not peer reviewed).
-/

public section

namespace Cslib.SignedDigitStream

open Finset

/-- Base margin `h_∘ = 16` for minimum-index dyadic band multiplication. -/
@[expose] def mulBaseMargin : ℕ := 16

/-- Lower inclusive endpoint of dyadic band `k` (`0` at `k = 0`, `2 ^ k` at `k + 1`). -/
@[expose] def bandStart : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 ^ k

/-- Upper exclusive endpoint of dyadic band `k` (`1` at `k = 0`, `2 ^ (k + 1)` at `k + 1`). -/
@[expose] def bandEnd : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 ^ (k + 1)

/-- Width `bandEnd k - bandStart k` of dyadic band `k`. -/
@[expose] def bandWidth (k : ℕ) : ℕ :=
  bandEnd k - bandStart k

/-- Unique band index `k` such that `bandStart k ≤ m < bandEnd k`. -/
@[expose] def bandIdx (m : ℕ) : ℕ :=
  if m = 0 then 0 else Nat.log 2 m + 1

/-- Band margin `h_k = h_∘ + ⌊bandStart k / 4⌋` [OpenAI2026LogSpace, Section 10.3]. -/
@[expose] def bandMargin (k : ℕ) : ℕ :=
  mulBaseMargin + bandStart k / 4

/-- Logarithmic cutoff band count above which all retained bands at clock `t` are empty. -/
@[expose] def maxBand (t : ℕ) : ℕ :=
  Nat.log 2 (t + mulBaseMargin) + 2

/-- Retained index pairs `(i, j)` in band `k` at output clock `t`. -/
@[expose] def bandPairs (t k : ℕ) : Finset (ℕ × ℕ) :=
  (range (t + bandMargin k + 1) ×ˢ range (t + bandMargin k + 1)).filter fun p =>
    bandStart k ≤ min p.1 p.2 ∧ min p.1 p.2 < bandEnd k ∧ p.1 + p.2 ≤ t + bandMargin k

/-- Exact mathematical integer sum `S_k` for band `k` at scale `2 ^ (t + bandMargin k)`
[OpenAI2026LogSpace, (10.6)]. -/
@[expose] def bandSum (x y : ℕ → ℤ) (t k : ℕ) : ℤ :=
  ∑ p ∈ bandPairs t k, x p.1 * y p.2 * (2 : ℤ) ^ (t + bandMargin k - (p.1 + p.2))

/-- Downward signed floor-shift fold across the `rem` highest active bands below `maxBand t`
[OpenAI2026LogSpace, (10.9)]. -/
@[expose] def bandFold (x y : ℕ → ℤ) (t : ℕ) : ℕ → ℤ
  | 0 => 0
  | rem + 1 =>
    let k := maxBand t - (rem + 1)
    let shift := bandMargin (k + 1) - bandMargin k
    bandSum x y t k + bandFold x y t rem / (2 : ℤ) ^ shift

/-- Scaled integer product approximation `⌊2 ^ (-h_0) F_0⌋` [OpenAI2026LogSpace, (10.9)]. -/
@[expose] def mulApprox (x y : ℕ → ℤ) (t : ℕ) : ℤ :=
  bandFold x y t (maxBand t) / (2 : ℤ) ^ mulBaseMargin

/-- Diagonal-windowed band pairs satisfying `t - q < i + j ≤ t + bandMargin k`
[OpenAI2026LogSpace, (10.10)]. -/
@[expose] def bandWindowPairs (t q k : ℕ) : Finset (ℕ × ℕ) :=
  (bandPairs t k).filter fun p => t < p.1 + p.2 + q

/-- Windowed integer sum omitting terms divisible by `2 ^ (q + bandMargin k)`. -/
@[expose] def bandWindowSum (x y : ℕ → ℤ) (t q k : ℕ) : ℤ :=
  ∑ p ∈ bandWindowPairs t q k, x p.1 * y p.2 * (2 : ℤ) ^ (t + bandMargin k - (p.1 + p.2))

/-- Modular downward band fold maintaining only the canonical `(q + bandMargin k)`-bit residue. -/
@[expose] def bandFoldMod (x y : ℕ → ℤ) (t q : ℕ) : ℕ → ℤ
  | 0 => 0
  | rem + 1 =>
    let k := maxBand t - (rem + 1)
    let shift := bandMargin (k + 1) - bandMargin k
    (bandWindowSum x y t q k + bandFoldMod x y t q rem / (2 : ℤ) ^ shift) %
      (2 : ℤ) ^ (q + bandMargin k)

/-- Mod-`2^q` residue of `mulApprox x y t` computed purely from windowed band residues. -/
@[expose] def mulResidue (x y : ℕ → ℤ) (t q : ℕ) : ℤ :=
  bandFoldMod x y t q (maxBand t) / (2 : ℤ) ^ mulBaseMargin

section BandGeometry

@[simp]
theorem bandStart_zero : bandStart 0 = 0 := rfl

@[simp]
theorem bandEnd_zero : bandEnd 0 = 1 := rfl

@[simp]
theorem bandMargin_zero : bandMargin 0 = mulBaseMargin := by
  simp [bandMargin]

theorem bandStart_succ_eq_bandEnd (k : ℕ) : bandStart (k + 1) = bandEnd k := by
  cases k <;> rfl

theorem bandStart_lt_bandEnd (k : ℕ) : bandStart k < bandEnd k := by
  cases k with
  | zero => decide
  | succ k =>
    simp only [bandStart, bandEnd]
    exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self k)

theorem bandStart_mono : Monotone bandStart := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [bandStart_succ_eq_bandEnd]
  exact (bandStart_lt_bandEnd k).le

theorem bandMargin_mono : Monotone bandMargin := by
  intro a b hab
  unfold bandMargin
  exact Nat.add_le_add_left (Nat.div_le_div_right (bandStart_mono hab)) _

theorem bandWidth_le_two_pow (k : ℕ) : bandWidth k ≤ 2 ^ k := by
  cases k with
  | zero => decide
  | succ k =>
    simp only [bandWidth, bandEnd, bandStart]
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

theorem mem_band_bandIdx (m : ℕ) : bandStart (bandIdx m) ≤ m ∧ m < bandEnd (bandIdx m) := by
  by_cases hm : m = 0
  · subst hm
    simp [bandIdx]
  · simp only [bandIdx, hm, ite_false, bandStart, bandEnd]
    exact ⟨Nat.pow_log_le_self 2 hm, Nat.lt_pow_succ_log_self (by decide) m⟩

theorem bandIdx_eq_iff {m k : ℕ} : bandIdx m = k ↔ bandStart k ≤ m ∧ m < bandEnd k := by
  constructor
  · rintro rfl
    exact mem_band_bandIdx m
  · rintro ⟨hlo, hhi⟩
    have hmem := mem_band_bandIdx m
    rcases lt_trichotomy (bandIdx m) k with hlt | heq | hgt
    · have hle : bandEnd (bandIdx m) ≤ bandStart k := by
        rw [← bandStart_succ_eq_bandEnd]
        exact bandStart_mono (Nat.succ_le_of_lt hlt)
      omega
    · exact heq
    · have hle : bandEnd k ≤ bandStart (bandIdx m) := by
        rw [← bandStart_succ_eq_bandEnd]
        exact bandStart_mono (Nat.succ_le_of_lt hgt)
      omega

theorem ten_add_two_mul_le_bandMargin (k : ℕ) : 10 + 2 * k ≤ bandMargin k := by
  rcases k with _ | _ | _ | m
  · decide
  · decide
  · decide
  · unfold bandMargin mulBaseMargin bandStart
    have hm : 2 * m ≤ 2 ^ m := by
      induction m with
      | zero => decide
      | succ n ih =>
        cases n with
        | zero => decide
        | succ n =>
          have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          calc 2 * (n + 1 + 1) = 2 * (n + 1) + 2 := by ring
            _ ≤ 2 ^ (n + 1) + 2 * 2 ^ n := Nat.add_le_add ih (by omega)
            _ = 2 ^ (n + 1 + 1) := by ring
    have hpow : 2 ^ (m + 2) / 4 = 2 ^ m := by
      have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
      rw [hp, Nat.mul_div_right _ (by decide)]
    rw [hpow]
    omega

theorem two_mul_bandStart_gt_of_maxBand_le {t k : ℕ} (hk : maxBand t ≤ k) :
    t + bandMargin k < 2 * bandStart k := by
  have hk2 : 2 ≤ k := by
    unfold maxBand at hk
    omega
  have hbase_lt : t + mulBaseMargin < bandStart (maxBand t) := by
    unfold maxBand bandStart
    exact Nat.lt_pow_succ_log_self (by decide) (t + mulBaseMargin)
  have hD_ge : bandStart (maxBand t) ≤ bandStart k := bandStart_mono hk
  have hD2 : 2 ≤ bandStart k := by
    have h2 : bandStart 2 = 2 := rfl
    rw [← h2]
    exact bandStart_mono hk2
  unfold bandMargin
  set D := bandStart k
  omega

/-- **Clock-drop latency inequality** [OpenAI2026LogSpace, (10.12)]: for any retained pair `(i, j)`
in a positive band `k + 1` (`D = 2 ^ k`), `4 * j + 3 * D ≤ 4 * (t + mulBaseMargin)` (and
symmetrically for `i`). -/
theorem three_mul_bandStart_le_four_mul_drop {t k : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ bandPairs t (k + 1)) :
    4 * p.1 + 3 * bandStart (k + 1) ≤ 4 * (t + mulBaseMargin) ∧
      4 * p.2 + 3 * bandStart (k + 1) ≤ 4 * (t + mulBaseMargin) := by
  obtain ⟨_, hlo, _, hsum⟩ := (mem_filter.mp hp)
  have hp1 : bandStart (k + 1) ≤ p.1 := hlo.trans (min_le_left _ _)
  have hp2 : bandStart (k + 1) ≤ p.2 := hlo.trans (min_le_right _ _)
  unfold bandMargin at hsum
  omega

/-- Every retained operand index `i` or `j` across all bands `k` obeys
`i ≤ t + mulBaseMargin` and `j ≤ t + mulBaseMargin`. -/
theorem index_le_clock_add_baseMargin {t k : ℕ} {p : ℕ × ℕ} (hp : p ∈ bandPairs t k) :
    p.1 ≤ t + mulBaseMargin ∧ p.2 ≤ t + mulBaseMargin := by
  cases k with
  | zero =>
    obtain ⟨_, _, _, hsum⟩ := mem_filter.mp hp
    rw [bandMargin_zero] at hsum
    omega
  | succ k =>
    have h := three_mul_bandStart_le_four_mul_drop hp
    omega

end BandGeometry

section ModularResidues

theorem bandSum_emod_eq_bandWindowSum_emod (x y : ℕ → ℤ) (t q k : ℕ) :
    bandSum x y t k % (2 : ℤ) ^ (q + bandMargin k) =
      bandWindowSum x y t q k % (2 : ℤ) ^ (q + bandMargin k) := by
  unfold bandSum bandWindowSum bandWindowPairs
  have hsplit := sum_filter_add_sum_filter_not (bandPairs t k) (fun p => t < p.1 + p.2 + q)
    (fun p => x p.1 * y p.2 * (2 : ℤ) ^ (t + bandMargin k - (p.1 + p.2)))
  rw [← hsplit]
  have hdvd : (2 : ℤ) ^ (q + bandMargin k) ∣
      ∑ p ∈ (bandPairs t k).filter (fun p => ¬ t < p.1 + p.2 + q),
        x p.1 * y p.2 * (2 : ℤ) ^ (t + bandMargin k - (p.1 + p.2)) := by
    refine dvd_sum fun p hp => ?_
    have hnot : ¬ t < p.1 + p.2 + q := (mem_filter.mp hp).2
    have hle : q + bandMargin k ≤ t + bandMargin k - (p.1 + p.2) := by omega
    exact dvd_mul_of_dvd_right (pow_dvd_pow 2 hle) _
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Int.add_mul_emod_self_left]

theorem bandFoldMod_eq_bandFold_emod (x y : ℕ → ℤ) (t q : ℕ) :
    ∀ rem ≤ maxBand t,
      bandFoldMod x y t q rem =
        bandFold x y t rem % (2 : ℤ) ^ (q + bandMargin (maxBand t - rem))
  | 0, _ => by simp [bandFoldMod, bandFold]
  | rem + 1, hrem => by
    simp only [bandFoldMod, bandFold]
    set k := maxBand t - (rem + 1)
    have hk_succ : maxBand t - rem = k + 1 := by omega
    have hle_rem : rem ≤ maxBand t := by omega
    have ih := bandFoldMod_eq_bandFold_emod x y t q rem hle_rem
    rw [hk_succ] at ih
    set shift := bandMargin (k + 1) - bandMargin k
    have hmargin_add : (q + bandMargin k) + shift = q + bandMargin (k + 1) := by
      have hmono : bandMargin k ≤ bandMargin (k + 1) := bandMargin_mono (Nat.le_succ k)
      omega
    have hdiv_mod : bandFoldMod x y t q rem / (2 : ℤ) ^ shift =
        (bandFold x y t rem / (2 : ℤ) ^ shift) % (2 : ℤ) ^ (q + bandMargin k) := by
      rw [ih, ← hmargin_add, ← ediv_two_pow_emod_eq]
    rw [hdiv_mod, Int.add_emod, ← bandSum_emod_eq_bandWindowSum_emod, Int.emod_emod,
      ← Int.add_emod]

/-- **Windowed modular product residue theorem** [OpenAI2026LogSpace, Lemma 10.4]:
`mulResidue x y t q` computes the exact mod-`2^q` Euclidean residue of `mulApprox x y t` while
retaining only diagonals `t - q < i + j ≤ t + bandMargin k` in each band. -/
theorem mulResidue_eq_mulApprox_emod (x y : ℕ → ℤ) (t q : ℕ) :
    mulResidue x y t q = mulApprox x y t % (2 : ℤ) ^ q := by
  unfold mulResidue mulApprox
  rw [bandFoldMod_eq_bandFold_emod x y t q (maxBand t) le_rfl, Nat.sub_self, bandMargin_zero,
    ← ediv_two_pow_emod_eq]

end ModularResidues

section ScaledAccuracy

private def retainedUnion (t K : ℕ) : Finset (ℕ × ℕ) :=
  (range K).biUnion (bandPairs t)

private theorem bandPairs_pairwiseDisjoint (t : ℕ) :
    (↑(range (maxBand t)) : Set ℕ).PairwiseDisjoint (bandPairs t) := by
  intro k₁ _ k₂ _ hne
  change Disjoint (bandPairs t k₁) (bandPairs t k₂)
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  obtain ⟨_, hlo₁, hhi₁, _⟩ := mem_filter.mp hp₁
  obtain ⟨_, hlo₂, hhi₂, _⟩ := mem_filter.mp hp₂
  have heq₁ : bandIdx (min p.1 p.2) = k₁ := bandIdx_eq_iff.mpr ⟨hlo₁, hhi₁⟩
  have heq₂ : bandIdx (min p.1 p.2) = k₂ := bandIdx_eq_iff.mpr ⟨hlo₂, hhi₂⟩
  exact hne (heq₁.symm.trans heq₂)

private theorem sum_bandPairs_real (x y : ℕ → ℤ) (t k : ℕ) :
    (bandSum x y t k : ℝ) / (2 : ℝ) ^ bandMargin k =
      ∑ p ∈ bandPairs t k,
        (2 : ℝ) ^ t * ((x p.1 : ℝ) * (y p.2 : ℝ) / (2 : ℝ) ^ (p.1 + p.2)) := by
  unfold bandSum
  rw [Int.cast_sum, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [← div_eq_mul_inv]
  obtain ⟨_, _, _, hle⟩ := mem_filter.mp hp
  push_cast
  have hpow : (2 : ℝ) ^ (t + bandMargin k - (p.1 + p.2)) * (2 : ℝ) ^ (p.1 + p.2) =
      (2 : ℝ) ^ t * (2 : ℝ) ^ bandMargin k := by
    rw [← pow_add, Nat.sub_add_cancel hle, pow_add]
  have hb_pos : (0 : ℝ) < (2 : ℝ) ^ bandMargin k := by positivity
  have hp_pos : (0 : ℝ) < (2 : ℝ) ^ (p.1 + p.2) := by positivity
  field_simp
  rw [mul_assoc ((x p.1 : ℝ) * (y p.2 : ℝ)), hpow]
  ring

private theorem abs_bandFold_sub_sum_le (x y : ℕ → ℤ) (t : ℕ) :
    ∀ rem ≤ maxBand t,
      |(bandFold x y t rem : ℝ) / (2 : ℝ) ^ bandMargin (maxBand t - rem) -
          ∑ k ∈ Ico (maxBand t - rem) (maxBand t),
            (bandSum x y t k : ℝ) / (2 : ℝ) ^ bandMargin k| ≤
        ∑ k ∈ Ico (maxBand t - rem) (maxBand t), 1 / (2 : ℝ) ^ bandMargin k
  | 0, _ => by simp [bandFold]
  | rem + 1, hrem => by
    simp only [bandFold]
    set k := maxBand t - (rem + 1)
    have hk_lt : k < maxBand t := by omega
    have hk_succ : maxBand t - rem = k + 1 := by omega
    have hle_rem : rem ≤ maxBand t := by omega
    have ih := abs_bandFold_sub_sum_le x y t rem hle_rem
    rw [hk_succ] at ih
    set s := bandMargin (k + 1) - bandMargin k
    have hs_add : bandMargin k + s = bandMargin (k + 1) := by
      have hm : bandMargin k ≤ bandMargin (k + 1) := bandMargin_mono (Nat.le_succ k)
      omega
    have hfl := abs_ediv_sub_div_lt_one (bandFold x y t rem)
      (by positivity : (0 : ℤ) < (2 : ℤ) ^ s)
    push_cast at hfl
    have hIco : Ico k (maxBand t) = insert k (Ico (k + 1) (maxBand t)) := by
      ext j
      simp only [mem_Ico, mem_insert]
      omega
    have hk_not_mem : k ∉ Ico (k + 1) (maxBand t) := by simp
    rw [hIco, sum_insert hk_not_mem, sum_insert hk_not_mem]
    set Q : ℝ := ((bandFold x y t rem / (2 : ℤ) ^ s : ℤ) : ℝ)
    set R : ℝ := (bandFold x y t rem : ℝ) / (2 : ℝ) ^ s
    set T : ℝ := ∑ j ∈ Ico (k + 1) (maxBand t), (bandSum x y t j : ℝ) / (2 : ℝ) ^ bandMargin j
    have hdiff : ((bandSum x y t k : ℝ) + Q) / (2 : ℝ) ^ bandMargin k -
        ((bandSum x y t k : ℝ) / (2 : ℝ) ^ bandMargin k + T) =
        (Q - R) / (2 : ℝ) ^ bandMargin k + (R / (2 : ℝ) ^ bandMargin k - T) := by ring
    have hR_div : R / (2 : ℝ) ^ bandMargin k =
        (bandFold x y t rem : ℝ) / (2 : ℝ) ^ bandMargin (k + 1) := by
      dsimp [R]
      rw [div_div, ← pow_add, add_comm s, hs_add]
    have hQ_err : |(Q - R) / (2 : ℝ) ^ bandMargin k| ≤ 1 / (2 : ℝ) ^ bandMargin k := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ bandMargin k)]
      exact div_le_div_of_nonneg_right hfl.le (by positivity)
    push_cast
    rw [hdiff]
    calc |(Q - R) / (2 : ℝ) ^ bandMargin k + (R / (2 : ℝ) ^ bandMargin k - T)|
        ≤ |(Q - R) / (2 : ℝ) ^ bandMargin k| + |R / (2 : ℝ) ^ bandMargin k - T| :=
          abs_add_le _ _
      _ ≤ 1 / (2 : ℝ) ^ bandMargin k +
            ∑ j ∈ Ico (k + 1) (maxBand t), 1 / (2 : ℝ) ^ bandMargin j := by
          rw [hR_div]
          exact add_le_add hQ_err ih

private theorem sum_floor_err_le (K : ℕ) :
    ∑ k ∈ range K, 1 / (2 : ℝ) ^ bandMargin k ≤ 1 / 768 := by
  have hterm : ∀ k ∈ range K, 1 / (2 : ℝ) ^ bandMargin k ≤ (1 / 1024) * (1 / 4 : ℝ) ^ k := by
    intro k _
    have hle := ten_add_two_mul_le_bandMargin k
    have hpow_le : (2 : ℝ) ^ (10 + 2 * k) ≤ (2 : ℝ) ^ bandMargin k :=
      pow_le_pow_right₀ (by norm_num) hle
    have h1 : 1 / (2 : ℝ) ^ bandMargin k ≤ 1 / (2 : ℝ) ^ (10 + 2 * k) :=
      one_div_le_one_div_of_le (by positivity) hpow_le
    have h2 : 1 / (2 : ℝ) ^ (10 + 2 * k) = (1 / 1024) * (1 / 4 : ℝ) ^ k := by
      have hp : (2 : ℝ) ^ (10 + 2 * k) = 1024 * (4 : ℝ) ^ k := by
        rw [pow_add, pow_mul]
        norm_num
      rw [hp, one_div_pow]
      field_simp
    exact h1.trans_eq h2
  calc ∑ k ∈ range K, 1 / (2 : ℝ) ^ bandMargin k
      ≤ ∑ k ∈ range K, (1 / 1024) * (1 / 4 : ℝ) ^ k := sum_le_sum hterm
    _ = (1 / 1024) * ∑ k ∈ range K, (1 / 4 : ℝ) ^ k := (mul_sum _ _ _).symm
    _ ≤ (1 / 1024) * (1 / (1 - (1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [Finset.range_eq_Ico, pow_zero] using
            geom_sum_Ico_le_of_lt_one (m := 0) (n := K) (by norm_num) (by norm_num))
          (by norm_num)
    _ = 1 / 768 := by norm_num

private theorem sum_ray_tail_le (N r M : ℕ) :
    ∑ j ∈ (range (N + 1)).filter (fun j => M < r + j), (1 / (2 : ℝ) ^ (r + j)) ≤
      1 / (2 : ℝ) ^ M := by
  set F := (range (N + 1)).filter fun j => M < r + j
  set g : ℕ → ℕ := fun j => r + j - (M + 1)
  have hinj : Set.InjOn g ↑F := by
    intro j₁ hj₁ j₂ hj₂ heq
    have h₁ : M < r + j₁ := (mem_filter.mp hj₁).2
    have h₂ : M < r + j₂ := (mem_filter.mp hj₂).2
    dsimp [g] at heq
    omega
  have hsub : F.image g ⊆ range (2 * N + r + 1) := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
    have hjN : j < N + 1 := (mem_filter.mp hj).1 |> mem_range.mp
    rw [mem_range]
    dsimp [g]
    omega
  have hrw : ∑ j ∈ F, (1 / (2 : ℝ) ^ (r + j)) =
      ∑ m ∈ F.image g, (1 / (2 : ℝ) ^ (M + 1)) * (1 / 2 : ℝ) ^ m := by
    rw [sum_image hinj]
    refine sum_congr rfl fun j hj => ?_
    have hM : M + 1 ≤ r + j := (mem_filter.mp hj).2
    have hadd : r + j = (M + 1) + g j := by
      dsimp [g]
      omega
    rw [hadd, pow_add, one_div_pow]
    ring
  rw [hrw]
  calc ∑ m ∈ F.image g, (1 / (2 : ℝ) ^ (M + 1)) * (1 / 2 : ℝ) ^ m
      ≤ ∑ m ∈ range (2 * N + r + 1), (1 / (2 : ℝ) ^ (M + 1)) * (1 / 2 : ℝ) ^ m :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (1 / (2 : ℝ) ^ (M + 1)) * ∑ m ∈ range (2 * N + r + 1), (1 / 2 : ℝ) ^ m :=
        (mul_sum _ _ _).symm
    _ ≤ (1 / (2 : ℝ) ^ (M + 1)) * (1 / (1 - (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [Finset.range_eq_Ico, pow_zero] using
            geom_sum_Ico_le_of_lt_one (m := 0) (n := 2 * N + r + 1) (by norm_num) (by norm_num))
          (by positivity)
    _ = 1 / (2 : ℝ) ^ M := by
        rw [pow_succ]
        field_simp
        ring

private theorem sum_omitted_le {x y : ℕ → ℤ} (hx : IsSignedStream x) (hy : IsSignedStream y)
    (t N : ℕ) (hN : t + bandMargin (maxBand t) ≤ N) :
    |∑ p ∈ range (N + 1) ×ˢ range (N + 1),
        (2 : ℝ) ^ t * ((x p.1 : ℝ) * (y p.2 : ℝ) / (2 : ℝ) ^ (p.1 + p.2)) -
      ∑ p ∈ retainedUnion t (maxBand t),
        (2 : ℝ) ^ t * ((x p.1 : ℝ) * (y p.2 : ℝ) / (2 : ℝ) ^ (p.1 + p.2))| ≤ 9 / 64 := by
  set K := maxBand t
  set Sq := range (N + 1) ×ˢ range (N + 1)
  set term : ℕ × ℕ → ℝ := fun p =>
    (2 : ℝ) ^ t * ((x p.1 : ℝ) * (y p.2 : ℝ) / (2 : ℝ) ^ (p.1 + p.2))
  have hret_sub : retainedUnion t K ⊆ Sq := by
    intro p hp
    unfold retainedUnion at hp
    rw [mem_biUnion] at hp
    obtain ⟨k, hk, hpk⟩ := hp
    have hk_le : k ≤ K := (mem_range.mp hk).le
    have hm_le : bandMargin k ≤ bandMargin K := bandMargin_mono hk_le
    obtain ⟨_, _, _, hsum⟩ := mem_filter.mp hpk
    rw [mem_product, mem_range, mem_range]
    omega
  rw [← sum_sdiff_eq_sub hret_sub]
  have hterm_bound : ∀ p : ℕ × ℕ, |term p| ≤ (2 : ℝ) ^ t * 36 * (1 / (2 : ℝ) ^ (p.1 + p.2)) := by
    intro p
    dsimp [term]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ t), abs_div,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (p.1 + p.2))]
    have hprod : |(x p.1 : ℝ)| * |(y p.2 : ℝ)| ≤ 36 := by
      have hx1 := hx.abs_cast_le p.1
      have hy1 := hy.abs_cast_le p.2
      nlinarith [abs_nonneg (x p.1 : ℝ), abs_nonneg (y p.2 : ℝ)]
    calc (2 : ℝ) ^ t * (|(x p.1 : ℝ)| * |(y p.2 : ℝ)| / (2 : ℝ) ^ (p.1 + p.2))
        ≤ (2 : ℝ) ^ t * (36 / (2 : ℝ) ^ (p.1 + p.2)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hprod (by positivity))
            (by positivity)
      _ = (2 : ℝ) ^ t * 36 * (1 / (2 : ℝ) ^ (p.1 + p.2)) := by ring
  have homit_gt : ∀ p ∈ Sq \ retainedUnion t K,
      t + bandMargin (bandIdx (min p.1 p.2)) < p.1 + p.2 := by
    intro p hp
    obtain ⟨hpSq, hpNot⟩ := mem_sdiff.mp hp
    set r := min p.1 p.2
    set k := bandIdx r
    by_cases hk : k < K
    · by_contra hle
      rw [not_lt] at hle
      have hp_mem : p ∈ bandPairs t k := by
        unfold bandPairs
        rw [mem_filter]
        have hband := mem_band_bandIdx r
        have hprod : p ∈ range (t + bandMargin k + 1) ×ˢ range (t + bandMargin k + 1) := by
          rw [mem_product, mem_range, mem_range]
          omega
        exact ⟨hprod, hband.1, hband.2, hle⟩
      exact hpNot (mem_biUnion.mpr ⟨k, mem_range.mpr hk, hp_mem⟩)
    · have hk_ge : K ≤ k := not_lt.mp hk
      have hgt := two_mul_bandStart_gt_of_maxBand_le hk_ge
      have hr_ge : bandStart k ≤ r := (mem_band_bandIdx r).1
      have hr_le : 2 * r ≤ p.1 + p.2 := by
        have h1 : r ≤ p.1 := min_le_left _ _
        have h2 : r ≤ p.2 := min_le_right _ _
        omega
      omega
  set w : ℕ × ℕ → ℝ := fun p => (2 : ℝ) ^ t * 36 * (1 / (2 : ℝ) ^ (p.1 + p.2))
  have habs_sum : |∑ p ∈ Sq \ retainedUnion t K, term p| ≤ ∑ p ∈ Sq \ retainedUnion t K, w p :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => hterm_bound p)
  have hpart := sum_filter_add_sum_filter_not (Sq \ retainedUnion t K) (fun p => p.1 ≤ p.2) w
  have hO1 : ∑ p ∈ (Sq \ retainedUnion t K).filter (fun p => p.1 ≤ p.2), w p ≤
      ∑ r ∈ range (N + 1), 36 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
    have hsub1 : (Sq \ retainedUnion t K).filter (fun p => p.1 ≤ p.2) ⊆
        Sq.filter (fun p => t + bandMargin (bandIdx p.1) < p.1 + p.2) := by
      intro p hp
      obtain ⟨hpDiff, hpLe⟩ := mem_filter.mp hp
      have hmin : min p.1 p.2 = p.1 := min_eq_left hpLe
      have hgt := homit_gt p hpDiff
      rw [hmin] at hgt
      exact mem_filter.mpr ⟨(mem_sdiff.mp hpDiff).1, hgt⟩
    calc ∑ p ∈ (Sq \ retainedUnion t K).filter (fun p => p.1 ≤ p.2), w p
        ≤ ∑ p ∈ Sq.filter (fun p => t + bandMargin (bandIdx p.1) < p.1 + p.2), w p :=
          sum_le_sum_of_subset_of_nonneg hsub1 fun _ _ _ => by dsimp [w]; positivity
      _ = ∑ r ∈ range (N + 1),
            ∑ j ∈ (range (N + 1)).filter (fun j => t + bandMargin (bandIdx r) < r + j),
              w (r, j) := by
          dsimp [Sq]
          rw [sum_filter, sum_product]
          refine sum_congr rfl fun r _ => ?_
          rw [sum_filter]
      _ ≤ ∑ r ∈ range (N + 1), 36 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
          refine sum_le_sum fun r _ => ?_
          dsimp [w]
          rw [← mul_sum]
          calc (2 : ℝ) ^ t * 36 *
                ∑ j ∈ (range (N + 1)).filter (fun j => t + bandMargin (bandIdx r) < r + j),
                  (1 / (2 : ℝ) ^ (r + j))
              ≤ (2 : ℝ) ^ t * 36 * (1 / (2 : ℝ) ^ (t + bandMargin (bandIdx r))) :=
                mul_le_mul_of_nonneg_left (sum_ray_tail_le N r _) (by positivity)
            _ = 36 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
                rw [pow_add]
                field_simp
  have hO2 : ∑ p ∈ (Sq \ retainedUnion t K).filter (fun p => ¬ p.1 ≤ p.2), w p ≤
      ∑ r ∈ range (N + 1), 36 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
    have hsub2 : (Sq \ retainedUnion t K).filter (fun p => ¬ p.1 ≤ p.2) ⊆
        Sq.filter (fun p => t + bandMargin (bandIdx p.2) < p.1 + p.2) := by
      intro p hp
      obtain ⟨hpDiff, hpGt⟩ := mem_filter.mp hp
      have hle : p.2 ≤ p.1 := (not_le.mp hpGt).le
      have hmin : min p.1 p.2 = p.2 := min_eq_right hle
      have hgt := homit_gt p hpDiff
      rw [hmin] at hgt
      exact mem_filter.mpr ⟨(mem_sdiff.mp hpDiff).1, hgt⟩
    calc ∑ p ∈ (Sq \ retainedUnion t K).filter (fun p => ¬ p.1 ≤ p.2), w p
        ≤ ∑ p ∈ Sq.filter (fun p => t + bandMargin (bandIdx p.2) < p.1 + p.2), w p :=
          sum_le_sum_of_subset_of_nonneg hsub2 fun _ _ _ => by dsimp [w]; positivity
      _ = ∑ r ∈ range (N + 1),
            ∑ i ∈ (range (N + 1)).filter (fun i => t + bandMargin (bandIdx r) < r + i),
              w (r, i) := by
          dsimp [Sq]
          rw [sum_filter, sum_product_right]
          refine sum_congr rfl fun r _ => ?_
          rw [sum_filter]
          refine sum_congr rfl fun i _ => ?_
          dsimp [w]
          rw [add_comm i r]
      _ ≤ ∑ r ∈ range (N + 1), 36 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
          refine sum_le_sum fun r _ => ?_
          dsimp [w]
          rw [← mul_sum]
          calc (2 : ℝ) ^ t * 36 *
                ∑ i ∈ (range (N + 1)).filter (fun i => t + bandMargin (bandIdx r) < r + i),
                  (1 / (2 : ℝ) ^ (r + i))
              ≤ (2 : ℝ) ^ t * 36 * (1 / (2 : ℝ) ^ (t + bandMargin (bandIdx r))) :=
                mul_le_mul_of_nonneg_left (sum_ray_tail_le N r _) (by positivity)
            _ = 36 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
                rw [pow_add]
                field_simp
  have hsum_r : ∑ r ∈ range (N + 1), 72 / (2 : ℝ) ^ bandMargin (bandIdx r) ≤ 9 / 64 := by
    set B := bandIdx N + 1
    have hcover : range (N + 1) ⊆ (range B).biUnion fun k => Ico (bandStart k) (bandEnd k) := by
      intro r hr
      have hr_le : r ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hr)
      refine mem_biUnion.mpr ⟨bandIdx r, mem_range.mpr ?_, ?_⟩
      · have hN_hi := (mem_band_bandIdx N).2
        have hr_lo := (mem_band_bandIdx r).1
        by_contra hge
        have hB_le : bandIdx N + 1 ≤ bandIdx r := not_lt.mp hge
        have hstart_le : bandEnd (bandIdx N) ≤ bandStart (bandIdx r) := by
          rw [← bandStart_succ_eq_bandEnd]
          exact bandStart_mono hB_le
        omega
      · rw [mem_Ico]
        exact mem_band_bandIdx r
    have hdisj : (↑(range B) : Set ℕ).PairwiseDisjoint fun k => Ico (bandStart k) (bandEnd k) := by
      intro k₁ _ k₂ _ hne
      change Disjoint (Ico (bandStart k₁) (bandEnd k₁)) (Ico (bandStart k₂) (bandEnd k₂))
      rw [Finset.disjoint_left]
      intro r hr₁ hr₂
      have heq₁ : bandIdx r = k₁ := bandIdx_eq_iff.mpr (mem_Ico.mp hr₁)
      have heq₂ : bandIdx r = k₂ := bandIdx_eq_iff.mpr (mem_Ico.mp hr₂)
      exact hne (heq₁.symm.trans heq₂)
    calc ∑ r ∈ range (N + 1), 72 / (2 : ℝ) ^ bandMargin (bandIdx r)
        ≤ ∑ r ∈ (range B).biUnion (fun k => Ico (bandStart k) (bandEnd k)),
            72 / (2 : ℝ) ^ bandMargin (bandIdx r) :=
          sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => by positivity
      _ = ∑ k ∈ range B, ∑ r ∈ Ico (bandStart k) (bandEnd k),
            72 / (2 : ℝ) ^ bandMargin (bandIdx r) := sum_biUnion hdisj
      _ = ∑ k ∈ range B, (bandWidth k : ℝ) * (72 / (2 : ℝ) ^ bandMargin k) := by
          refine sum_congr rfl fun k _ => ?_
          have hconst : ∀ r ∈ Ico (bandStart k) (bandEnd k),
              72 / (2 : ℝ) ^ bandMargin (bandIdx r) = 72 / (2 : ℝ) ^ bandMargin k := by
            intro r hr
            rw [bandIdx_eq_iff.mpr (mem_Ico.mp hr)]
          rw [sum_congr rfl hconst, sum_const, Nat.card_Ico, nsmul_eq_mul]
          rfl
      _ ≤ ∑ k ∈ range B, (72 / 1024) * (1 / 2 : ℝ) ^ k := by
          refine sum_le_sum fun k _ => ?_
          have hw_le : (bandWidth k : ℝ) ≤ (2 : ℝ) ^ k := by
            exact_mod_cast bandWidth_le_two_pow k
          have hm_le : (2 : ℝ) ^ (10 + 2 * k) ≤ (2 : ℝ) ^ bandMargin k :=
            pow_le_pow_right₀ (by norm_num) (ten_add_two_mul_le_bandMargin k)
          calc (bandWidth k : ℝ) * (72 / (2 : ℝ) ^ bandMargin k)
              ≤ (2 : ℝ) ^ k * (72 / (2 : ℝ) ^ (10 + 2 * k)) :=
                mul_le_mul hw_le
                  (div_le_div_of_nonneg_left (by norm_num) (by positivity) hm_le)
                  (by positivity) (by positivity)
            _ = (72 / 1024) * (1 / 2 : ℝ) ^ k := by
                have hp : (2 : ℝ) ^ (10 + 2 * k) = 1024 * ((2 : ℝ) ^ k * (2 : ℝ) ^ k) := by
                  rw [pow_add, two_mul, pow_add]
                  norm_num
                rw [hp, one_div_pow]
                field_simp
      _ = (72 / 1024) * ∑ k ∈ range B, (1 / 2 : ℝ) ^ k := (mul_sum _ _ _).symm
      _ ≤ (72 / 1024) * (1 / (1 - (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (by simpa only [Finset.range_eq_Ico, pow_zero] using
              geom_sum_Ico_le_of_lt_one (m := 0) (n := B) (by norm_num) (by norm_num))
            (by norm_num)
      _ = 9 / 64 := by norm_num
  have htwo : ∑ r ∈ range (N + 1), 36 / (2 : ℝ) ^ bandMargin (bandIdx r) +
      ∑ r ∈ range (N + 1), 36 / (2 : ℝ) ^ bandMargin (bandIdx r) =
      ∑ r ∈ range (N + 1), 72 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun r _ => by ring
  linarith

/-- **Lemma 10.4 (scaled product approximation)** [OpenAI2026LogSpace, Lemma 10.4]: for any two
signed-digit streams `x, y`, `mulApprox x y` approximates `streamVal x * streamVal y` within
scaled error `< 2`. -/
theorem mulApprox_isScaledApprox {x y : ℕ → ℤ}
    (hx : IsSignedStream x) (hy : IsSignedStream y) :
    IsScaledApprox (streamVal x * streamVal y) (mulApprox x y) := by
  intro t
  unfold mulApprox
  set K := maxBand t
  set N := t + bandMargin K + 20
  set term : ℕ × ℕ → ℝ := fun p =>
    (2 : ℝ) ^ t * ((x p.1 : ℝ) * (y p.2 : ℝ) / (2 : ℝ) ^ (p.1 + p.2))
  have hfl := abs_ediv_sub_div_lt_one (bandFold x y t K)
    (by positivity : (0 : ℤ) < (2 : ℤ) ^ mulBaseMargin)
  push_cast at hfl
  have hfold_err : |(bandFold x y t K : ℝ) / (2 : ℝ) ^ mulBaseMargin -
      ∑ p ∈ retainedUnion t K, term p| ≤ 1 / 768 := by
    have h1 := abs_bandFold_sub_sum_le x y t K le_rfl
    rw [Nat.sub_self, bandMargin_zero, ← Finset.range_eq_Ico] at h1
    have hret_eq : ∑ k ∈ range K, (bandSum x y t k : ℝ) / (2 : ℝ) ^ bandMargin k =
        ∑ p ∈ retainedUnion t K, term p := by
      unfold retainedUnion
      rw [sum_biUnion (bandPairs_pairwiseDisjoint t)]
      refine sum_congr rfl fun k _ => sum_bandPairs_real x y t k
    rw [hret_eq] at h1
    exact h1.trans (sum_floor_err_le K)
  have hSq_eq : ∑ p ∈ range (N + 1) ×ˢ range (N + 1), term p =
      (2 : ℝ) ^ t * (streamPrefix x N * streamPrefix y N) := by
    unfold streamPrefix
    rw [sum_mul_sum, mul_sum, sum_product]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    dsimp [term]
    rw [pow_add]
    field_simp
  have homit := sum_omitted_le hx hy t N (by dsimp [N, K]; omega)
  rw [hSq_eq] at homit
  have hpre_err : |(2 : ℝ) ^ t * (streamPrefix x N * streamPrefix y N) -
      (2 : ℝ) ^ t * (streamVal x * streamVal y)| ≤ 144 / (2 : ℝ) ^ 20 := by
    have hx_pre : |streamPrefix x N| ≤ 12 := by
      have h := abs_streamPrefix_le hx N
      have hpos : (0 : ℝ) ≤ 6 / (2 : ℝ) ^ N := by positivity
      linarith
    have hy_val : |streamVal y| ≤ 12 := abs_streamVal_le_twelve hy
    have hx_tail := abs_streamVal_sub_streamPrefix_le hx N
    have hy_tail := abs_streamVal_sub_streamPrefix_le hy N
    rw [abs_sub_comm] at hx_tail hy_tail
    have hdecomp : streamPrefix x N * streamPrefix y N - streamVal x * streamVal y =
        streamPrefix x N * (streamPrefix y N - streamVal y) +
          (streamPrefix x N - streamVal x) * streamVal y := by ring
    have hprod_err : |streamPrefix x N * streamPrefix y N - streamVal x * streamVal y| ≤
        144 / (2 : ℝ) ^ N := by
      rw [hdecomp]
      calc |streamPrefix x N * (streamPrefix y N - streamVal y) +
            (streamPrefix x N - streamVal x) * streamVal y|
          ≤ |streamPrefix x N * (streamPrefix y N - streamVal y)| +
              |(streamPrefix x N - streamVal x) * streamVal y| := abs_add_le _ _
        _ = |streamPrefix x N| * |streamPrefix y N - streamVal y| +
              |streamPrefix x N - streamVal x| * |streamVal y| := by rw [abs_mul, abs_mul]
        _ ≤ 12 * (6 / (2 : ℝ) ^ N) + (6 / (2 : ℝ) ^ N) * 12 :=
              add_le_add (mul_le_mul hx_pre hy_tail (abs_nonneg _) (by norm_num))
                (mul_le_mul hx_tail hy_val (abs_nonneg _) (by positivity))
        _ = 144 / (2 : ℝ) ^ N := by ring
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ t)]
    have hN_ge : t + 20 ≤ N := by omega
    have hpow_ge : (2 : ℝ) ^ t * (2 : ℝ) ^ 20 ≤ (2 : ℝ) ^ N := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num) hN_ge
    calc (2 : ℝ) ^ t * |streamPrefix x N * streamPrefix y N - streamVal x * streamVal y|
        ≤ (2 : ℝ) ^ t * (144 / (2 : ℝ) ^ N) :=
          mul_le_mul_of_nonneg_left hprod_err (by positivity)
      _ ≤ (2 : ℝ) ^ t * (144 / ((2 : ℝ) ^ t * (2 : ℝ) ^ 20)) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow_ge) (by positivity)
      _ = 144 / (2 : ℝ) ^ 20 := by field_simp
  have htri1 := abs_sub_le ((bandFold x y t K / (2 : ℤ) ^ mulBaseMargin : ℤ) : ℝ)
    ((bandFold x y t K : ℝ) / (2 : ℝ) ^ mulBaseMargin)
    (∑ p ∈ retainedUnion t K, term p)
  have htri2 := abs_sub_le ((bandFold x y t K / (2 : ℤ) ^ mulBaseMargin : ℤ) : ℝ)
    (∑ p ∈ retainedUnion t K, term p)
    ((2 : ℝ) ^ t * (streamPrefix x N * streamPrefix y N))
  have htri3 := abs_sub_le ((bandFold x y t K / (2 : ℤ) ^ mulBaseMargin : ℤ) : ℝ)
    ((2 : ℝ) ^ t * (streamPrefix x N * streamPrefix y N))
    ((2 : ℝ) ^ t * (streamVal x * streamVal y))
  rw [abs_sub_comm (∑ p ∈ retainedUnion t K, term p)] at htri2
  have hnum : (1 : ℝ) + 1 / 768 + 9 / 64 + 144 / (2 : ℝ) ^ 20 < 2 := by norm_num
  linarith

end ScaledAccuracy

end Cslib.SignedDigitStream
