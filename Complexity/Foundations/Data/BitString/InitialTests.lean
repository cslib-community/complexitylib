/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Weight
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Log
import Complexity.Foundations.Combinatorics.Expander.TannerCode
import Complexity.Foundations.Data.Code.HammingBound
import Complexity.Probability.SmallBias.Random
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Initial parity tests from a Tanner code

[OpenAI2026ETH, Lemma 6.1] constructs, for a formula with `m ≤ B n` clauses, at most `3 n` sparse
parity tests on the `m` clause-violation bits whose common kernel contains no nonzero vector of
weight less than `m / P`, where `μ = ⌊log₂ m⌋ + 1`, `P = 20000 B² μ²`, and each test reads at most
`D₀ = 320000 B² μ³` bits. This file proves that such tests exist
(`Cslib.BitString.exists_initialTests`); computing them by exhaustive search, and the cost of that
search, are not treated here.

The tests are a shortened Tanner code (`Cslib.BitString.Tanner.le_weight_of_shortRow`). With
`d = min(m, D₀)` and `q = 2 ^ ℓ` least with `q d ≥ m`, the graph is the double cover of a Cayley
graph of the cube `Fin ℓ → Bool` with `d` generators that are `ε`-biased for `ε = 1 / (200 B μ)`
(`Cslib.BitString.exists_isSmallBias_map_of_exp_lt`; if `ℓ = 0` there is nothing to check). The
local code has `c = ⌈d / (8 B)⌉` checks and distance more than `h = ⌈d / (100 B μ)⌉ - 1`
(`Cslib.BitString.exists_forall_weight_le`), as at most `(d + 1) ^ h < 2 ^ c` nonzero strings have
weight at most `h` (`Cslib.BitString.card_filter_weight_le_le`). The distance bound
`(h + 1)(h + 1 - ε d) q ≤ d · weight` then gives weight at least `q d / P ≥ m / P`, and there are
`2 q c ≤ 3 n` rows of at most `d ≤ D₀` ones.

## Main results

* `Cslib.BitString.card_filter_weight_le_le`: at most `(d + 1) ^ h` strings have weight at most `h`.
* `Cslib.BitString.exists_initialTests`: the initial parity tests of [OpenAI2026ETH, Lemma 6.1].

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6.1
-/

@[expose] public section

namespace Cslib.BitString

open Finset Cslib.BitString.Tanner Cslib.RotationMap Cslib.Probability.PMF

/-- At most `(d + 1) ^ h` strings of length `d` have weight at most `h`. -/
theorem card_filter_weight_le_le (d h : ℕ) : #{w : Fin d → Bool | weight w ≤ h} ≤ (d + 1) ^ h := by
  have hball := Cslib.Code.card_filter_hammingDist_le_eq_sum (β := fun _ : Fin d => Bool)
    (0 : Fin d → Bool) h
  have hsph : ∀ j, #{y : Fin d → Bool | hammingDist (0 : Fin d → Bool) y = j} = d.choose j := by
    intro j
    rw [Cslib.Code.card_filter_hammingDist_eq_choose_mul_pow (q := 2) (fun _ => by simp)]
    simp
  have hset : ({w : Fin d → Bool | weight w ≤ h} : Finset (Fin d → Bool)) =
      ({y : Fin d → Bool | hammingDist (0 : Fin d → Bool) y ≤ h} : Finset (Fin d → Bool)) := by
    ext w
    simp [weight_eq_hammingNorm, hammingDist_comm, hammingDist_zero_right]
  rw [hset, hball]
  simp only [hsph]
  calc ∑ j ∈ range (h + 1), d.choose j ≤ ∑ j ∈ range (h + 1), d ^ j * 1 ^ (h - j) * h.choose j :=
        sum_le_sum fun j hj => by
          have : 1 ≤ h.choose j := Nat.choose_pos (Nat.lt_succ_iff.mp (mem_range.mp hj))
          calc d.choose j ≤ d ^ j := Nat.choose_le_pow d j
            _ ≤ d ^ j * 1 ^ (h - j) * h.choose j := by
              rw [one_pow, mul_one]; exact Nat.le_mul_of_pos_right _ this
    _ = (d + 1) ^ h := (add_pow d 1 h).symm

/-- The shift-existence condition with the constants of [OpenAI2026ETH]: for `B, μ ≥ 1` and
`ℓ ≤ μ + 1`, `2 · 2 ^ ℓ · exp(-ε² D₀ / 2) < 1` with `ε = 1 / (200 B μ)` and `D₀ = 320000 B² μ³`,
since `ε² D₀ / 2 = 4 μ` and `2 ^ (μ + 2) ≤ 8 ^ μ < e ^ (4 μ)`. -/
private theorem shift_condition {B μ ℓ : ℕ} (hB : 1 ≤ B) (hμ : 1 ≤ μ) (hℓ : ℓ ≤ μ + 1) :
    2 * 2 ^ Fintype.card (Fin ℓ) * Real.exp (-((1 / (200 * B * μ : ℝ)) ^ 2 *
      ((320000 * B ^ 2 * μ ^ 3 : ℕ) : ℝ) / 2)) < 1 := by
  rw [Fintype.card_fin]
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hμr : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
  have hexp : (1 / (200 * B * μ : ℝ)) ^ 2 * ((320000 * B ^ 2 * μ ^ 3 : ℕ) : ℝ) / 2 = 4 * μ := by
    push_cast
    field_simp
    ring
  rw [hexp]
  have h8 : (2 : ℝ) * 2 ^ ℓ ≤ 8 ^ μ := by
    have : (2 : ℝ) * 2 ^ ℓ ≤ 2 ^ (μ + 2) := by
      rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
    refine this.trans ?_
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have he4 : (8 : ℝ) < Real.exp 4 := by
    have := Real.exp_one_gt_two
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h4]; nlinarith [pow_lt_pow_left₀ this (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)]
  have hpow : (8 : ℝ) ^ μ < Real.exp (4 * μ) := by
    rw [show (4 : ℝ) * μ = μ * 4 by ring, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ he4 (by norm_num) (by omega)
  have hpos := Real.exp_pos (4 * μ)
  rw [Real.exp_neg]
  rw [mul_inv_lt_iff₀ hpos, one_mul]
  linarith

/-- The quotient `⌈d / N⌉ = (d + N - 1) / N` satisfies `d ≤ N ⌈d / N⌉` and
`N (⌈d / N⌉ - 1) < d`. -/
private theorem le_mul_ceilDiv_and_lt {N : ℕ} (hN : 0 < N) {d : ℕ} (hd : 0 < d) :
    d ≤ N * ((d + N - 1) / N) ∧ N * ((d + N - 1) / N - 1) < d := by
  have h1 := Nat.div_add_mod (d + N - 1) N
  have h2 := Nat.mod_lt (d + N - 1) hN
  set q := (d + N - 1) / N
  set r := (d + N - 1) % N
  refine ⟨by omega, ?_⟩
  rw [Nat.mul_sub, mul_one]
  omega

/-- The row count when `q = 1`: `2 c ≤ 3 n` for `c = ⌈d / (8 B)⌉` and `d ≤ m ≤ B n`. -/
private theorem two_mul_le_of_le {n m d c B : ℕ} (hn : 1 ≤ n) (hm : m ≤ B * n)
    (hdm : d ≤ m) (hc : 8 * B * c < d + 8 * B) : 2 * c ≤ 3 * n := by
  have h1 : B * (8 * c) < B * (n + 8) := by
    calc B * (8 * c) = 8 * B * c := by ring
      _ < d + 8 * B := hc
      _ ≤ B * n + 8 * B := by omega
      _ = B * (n + 8) := by ring
  have := Nat.lt_of_mul_lt_mul_left h1
  omega

/-- The row count when `q > 1`: `2 q c ≤ 3 n` for `c = ⌈D₀ / (8 B)⌉`, `D₀ ≥ 8 B`, `q D₀ < 2 m` and
`m ≤ B n`. -/
private theorem two_mul_pow_mul_le {n m D c B ℓ : ℕ} (hm : m ≤ B * n)
    (hD : 8 * B ≤ D) (hc : 8 * B * c < D + 8 * B) (hq : 2 ^ ℓ * D < 2 * m) :
    2 * (2 ^ ℓ * c) ≤ 3 * n := by
  set q := 2 ^ ℓ
  have hq0 : 0 < q := by positivity
  have h3 : 8 * B * c < 2 * D := by omega
  have h4 : q * (8 * B * c) < q * (2 * D) := Nat.mul_lt_mul_of_pos_left h3 hq0
  have h2 : B * (4 * (q * c)) < B * (2 * n) := by nlinarith
  have := Nat.lt_of_mul_lt_mul_left h2
  omega

/-- The distance arithmetic of [OpenAI2026ETH, Lemma 6.1]: from the Tanner bound with
`k ≥ d / (100 B μ)` and `ε = 1 / (200 B μ)`, the weight is at least `q d / P ≥ m / P`. -/
private theorem le_of_tanner_bound {B μ d k ℓ m w : ℕ} (hB : 1 ≤ B) (hμ : 1 ≤ μ) (hd : 1 ≤ d)
    (hk_ge : d ≤ 100 * B * μ * k) (hℓ : m ≤ 2 ^ ℓ * d)
    (hw : (k : ℝ) * (k - 1 / (200 * B * μ : ℝ) * d) * 2 ^ ℓ ≤ d * w) :
    m ≤ 20000 * B ^ 2 * μ ^ 2 * w := by
  set N : ℕ := 100 * B * μ with hN
  have hNR : (N : ℝ) = 100 * B * μ := by rw [hN]; push_cast; ring
  have hNpos' : (0 : ℝ) < N := by rw [hNR]; positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hkR : (d : ℝ) ≤ N * k := by exact_mod_cast hk_ge
  have hεd : 1 / (200 * B * μ : ℝ) * d = d / (2 * N) := by
    rw [hNR]; field_simp; ring
  rw [hεd] at hw
  set a : ℝ := (d : ℝ) / N
  have ha : a ≤ k := by rw [div_le_iff₀ hNpos']; linarith
  have ha0 : 0 ≤ a := by positivity
  have hk2 : a / 2 ≤ (k : ℝ) - d / (2 * N) := by
    have : (d : ℝ) / (2 * N) = a / 2 := by simp only [a]; field_simp
    rw [this]; linarith
  have hprod : a * (a / 2) ≤ (k : ℝ) * ((k : ℝ) - d / (2 * N)) :=
    mul_le_mul ha hk2 (by positivity) (by linarith)
  have hq : (0 : ℝ) < 2 ^ ℓ := by positivity
  have h1 : a * (a / 2) * 2 ^ ℓ ≤ d * w := (mul_le_mul_of_nonneg_right hprod hq.le).trans hw
  have h2 : (d : ℝ) * 2 ^ ℓ ≤ 2 * N ^ 2 * w := by
    have e : a * (a / 2) * 2 ^ ℓ = d * (d * 2 ^ ℓ / (2 * N ^ 2)) := by
      simp only [a]; field_simp
    rw [e] at h1
    have := le_of_mul_le_mul_left h1 hdR
    rwa [div_le_iff₀ (by positivity), mul_comm (w : ℝ) _] at this
  have hmR : (m : ℝ) ≤ 2 ^ ℓ * d := by exact_mod_cast hℓ
  have : (m : ℝ) ≤ 20000 * B ^ 2 * μ ^ 2 * w := by
    rw [hNR] at h2; nlinarith
  exact_mod_cast this

/-- **Initial parity tests** [OpenAI2026ETH, Lemma 6.1]. Let `n, B ≥ 1` and `m ≤ B n`, and put
`μ = ⌊log₂ m⌋ + 1`, `P = 20000 B² μ²` and `D₀ = 320000 B² μ³`. There are at most `3 n` rows over
`Fin m`, each with at most `D₀` ones, such that every nonzero bit string orthogonal to all of them
has at least `m / P` ones. -/
theorem exists_initialTests {n m B : ℕ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hm : m ≤ B * n) :
    ∃ rows : List (Fin m → Bool), rows.length ≤ 3 * n ∧
      (∀ r ∈ rows, weight r ≤ 320000 * B ^ 2 * (Nat.log 2 m + 1) ^ 3) ∧
      ∀ z : Fin m → Bool, z ≠ 0 → (∀ r ∈ rows, r ⬝ᵥ z = false) →
        m ≤ 20000 * B ^ 2 * (Nat.log 2 m + 1) ^ 2 * weight z := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact ⟨[], by simp, by simp, fun z hz => absurd (funext fun i => i.elim0) hz⟩
  set μ := Nat.log 2 m + 1 with hμdef
  have hμ : 1 ≤ μ := by omega
  have hmμ : m < 2 ^ μ := Nat.lt_pow_succ_log_self (by norm_num) m
  set D0 := 320000 * B ^ 2 * μ ^ 3 with hD0
  have hD0B : 8 * B ≤ D0 := by
    have : 1 ≤ B * μ ^ 3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  set d := min m D0 with hddef
  have hd : 1 ≤ d := le_min hm0 (by omega)
  have hdm : d ≤ m := min_le_left _ _
  have hdD : d ≤ D0 := min_le_right _ _
  have : NeZero d := ⟨by omega⟩
  -- the number of vertices on each side, `q = 2 ^ ℓ`, least with `m ≤ q d`
  have hex : ∃ a, m ≤ 2 ^ a * d :=
    ⟨m, (Nat.lt_two_pow_self).le.trans (Nat.le_mul_of_pos_right _ hd)⟩
  set ℓ := Nat.find hex with hℓdef
  have hℓ : m ≤ 2 ^ ℓ * d := Nat.find_spec hex
  have hℓmin : 0 < ℓ → 2 ^ ℓ * d < 2 * m := fun h => by
    have h1 : ¬ m ≤ 2 ^ (ℓ - 1) * d := Nat.find_min hex (Nat.sub_lt h one_pos)
    rw [not_le] at h1
    rw [show ℓ = ℓ - 1 + 1 by omega, pow_succ]
    nlinarith
  have hℓd : 0 < ℓ → d = D0 := fun h => by
    by_contra hne
    have hdm' : d = m := by
      rcases le_total m D0 with h' | h'
      · exact min_eq_left h'
      · exact absurd (min_eq_right h') hne
    have : ℓ ≤ 0 := Nat.find_min' hex (by rw [hdm']; simp)
    omega
  have hℓμ : ℓ ≤ μ + 1 := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · omega
    · have h1 := hℓmin h
      have h2 : 2 ^ ℓ < 2 ^ (μ + 1) := by
        calc 2 ^ ℓ ≤ 2 ^ ℓ * d := Nat.le_mul_of_pos_right _ hd
          _ < 2 * m := h1
          _ < 2 * 2 ^ μ := by omega
          _ = 2 ^ (μ + 1) := by rw [pow_succ]; ring
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2 |>.le
  -- `ε`-biased shifts
  obtain ⟨s, hs⟩ : ∃ s : Fin d → Fin ℓ → Bool,
      IsSmallBias (1 / (200 * B * μ : ℝ)) ((uniformOfFintype (Fin d)).map s) := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · refine ⟨fun _ => 0, fun S hS => ?_⟩
      obtain ⟨i, -⟩ := hS
      exact absurd i.2 (by omega)
    · refine exists_isSmallBias_map_of_exp_lt (by positivity) ?_
      have := shift_condition hB hμ hℓμ
      rwa [show ((320000 * B ^ 2 * μ ^ 3 : ℕ) : ℝ) = (d : ℝ) by rw [hℓd hpos]] at this
  -- the local code: `c = ⌈d / (8 B)⌉` checks of distance more than `h = ⌈d / (100 B μ)⌉ - 1`
  set N := 100 * B * μ with hN
  have hNpos : 0 < N := by positivity
  set k := (d + N - 1) / N with hkdef
  obtain ⟨hk_ge, hk_lt⟩ := le_mul_ceilDiv_and_lt hNpos hd
  rw [← hkdef] at hk_ge hk_lt
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, mul_zero] at hk_ge; omega
    · exact hk0
  set h := k - 1 with hhdef
  have h8B : 0 < 8 * B := by omega
  set c := (d + 8 * B - 1) / (8 * B) with hcdef
  obtain ⟨hc_ge, hc_lt'⟩ := le_mul_ceilDiv_and_lt h8B hd
  rw [← hcdef] at hc_ge hc_lt'
  have hc_lt : 8 * B * c < d + 8 * B := by
    rcases Nat.eq_zero_or_pos c with hc0 | hc0
    · rw [hc0]; omega
    · have : 8 * B * c = 8 * B * (c - 1) + 8 * B := by
        rw [Nat.mul_sub, mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hc0)]
      omega
  have hμh : μ * h < c := by
    have h1 : B * (100 * (μ * h)) < B * (8 * c) := by
      have : N * h = B * (100 * (μ * h)) := by rw [hN]; ring
      calc B * (100 * (μ * h)) = N * h := this.symm
        _ < d := hk_lt
        _ ≤ 8 * B * c := hc_ge
        _ = B * (8 * c) := by ring
    have h2 := Nat.lt_of_mul_lt_mul_left h1
    omega
  obtain ⟨A, hA⟩ : ∃ A : Fin c → Fin d → Bool,
      ∀ w, w ≠ 0 → weight w ≤ h → ∃ i, A i ⬝ᵥ w = true := by
    refine exists_forall_weight_le ?_
    calc #{w : Fin d → Bool | w ≠ 0 ∧ weight w ≤ h}
        ≤ #{w : Fin d → Bool | weight w ≤ h} :=
          card_le_card fun w hw => by simp only [mem_filter, mem_univ, true_and] at hw ⊢; exact hw.2
      _ ≤ (d + 1) ^ h := card_filter_weight_le_le d h
      _ ≤ (2 ^ μ) ^ h := Nat.pow_le_pow_left (by omega) h
      _ = 2 ^ (μ * h) := by rw [← pow_mul]
      _ < 2 ^ c := Nat.pow_lt_pow_right (by norm_num) hμh
  have hAd : ∀ w : Fin d → Bool, w ≠ 0 → (∀ i, A i ⬝ᵥ w = false) → h < weight w := by
    intro w hw hker
    by_contra hle
    obtain ⟨i, hi⟩ := hA w hw (not_lt.mp hle)
    rw [hker i] at hi
    exact Bool.false_ne_true hi
  -- keep `m` of the `2 ^ ℓ d` edges
  have hcard : m ≤ Fintype.card ((Fin ℓ → Bool) × Fin d) := by
    simpa [Fintype.card_prod, Fintype.card_fun] using hℓ
  let emb : Fin m ↪ (Fin ℓ → Bool) × Fin d :=
    (Fin.castLEEmb hcard).trans (Fintype.equivFin _).symm.toEmbedding
  refine ⟨(univ : Finset (Bool × (Fin ℓ → Bool) × Fin c)).toList.map (shortRow s A emb),
    ?_, ?_, ?_⟩
  · -- `2 q c ≤ 3 n` rows
    rw [List.length_map, length_toList, card_univ, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin]
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · rw [h0, pow_zero, one_mul]
      exact two_mul_le_of_le hn hm hdm hc_lt
    · rw [hℓd hpos] at hc_lt
      exact two_mul_pow_mul_le hm hD0B hc_lt (by rw [← hℓd hpos]; exact hℓmin hpos)
  · -- rows of weight at most `d ≤ D₀`
    intro r hr
    obtain ⟨r', -, rfl⟩ := List.mem_map.mp hr
    exact (weight_shortRow_le s A emb r').trans hdD
  · -- the distance
    intro z hz0 hz
    have hz' : ∀ r, shortRow s A emb r ⬝ᵥ z = false := fun r =>
      hz _ (List.mem_map.mpr ⟨r, mem_toList.mpr (mem_univ r), rfl⟩)
    have hw := le_weight_of_shortRow s (by positivity) hs A hAd emb hz' hz0
    rw [show h + 1 = k by omega] at hw
    exact le_of_tanner_bound hB hμ hd hk_ge hℓ hw

end Cslib.BitString
