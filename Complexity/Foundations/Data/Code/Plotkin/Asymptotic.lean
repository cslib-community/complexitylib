/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Complexity.Foundations.Data.Code.Plotkin

/-!
# The asymptotic Plotkin bound

Let `C` be a code of length `n` and minimum distance at least `d > 0` over `q ≥ 2` letters, with
`q d ≤ (q - 1) n`. Shortening `C` to the largest number `m` of coordinates with `(q - 1) m < q d`
and applying the Plotkin bound to each of the `q ^ (n - m)` shortened codes
(`Cslib.Code.card_mul_sub_le_pow_mul_of_le_minDist`) gives
`log_q |C| ≤ n - q d / (q - 1) + 2 + log_q d` (`Cslib.Code.logb_card_le_of_le_minDist`). For a
family of codes of relative distance at least `δ ≤ 1 - 1 / q` and growing length, this is the
**asymptotic Plotkin bound** `R ≤ 1 - q δ / (q - 1) + o(1)` on the rate `R`
(`Cslib.Code.eventually_logb_card_le_of_le_hammingDist`) [GuruswamiRudraSudan2019,
Corollary 4.4.2].

## Main results

* `Cslib.Code.logb_card_le_of_le_minDist`: the Plotkin bound below relative distance `1 - 1 / q`,
  logarithmic form.
* `Cslib.Code.eventually_logb_card_le_of_le_hammingDist`: the asymptotic Plotkin bound.

## References

* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
-/

public section

namespace Cslib.Code

open Finset

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

/-- **The Plotkin bound below relative distance `1 - 1 / q`**, logarithmic form: a code of length
`n` and minimum distance at least `d > 0` over `q ≥ 2` letters with `q d ≤ (q - 1) n` satisfies
`log_q |C| ≤ n - q d / (q - 1) + 2 + log_q d`. -/
theorem logb_card_le_of_le_minDist [Nontrivial α] {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (hd0 : 0 < d)
    (h : Fintype.card α * d ≤ (Fintype.card α - 1) * Fintype.card ι) :
    Real.logb (Fintype.card α) #C ≤
      Fintype.card ι - Fintype.card α * d / (Fintype.card α - 1) + 2 +
        Real.logb (Fintype.card α) d := by
  set q := Fintype.card α
  set n := Fintype.card ι
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hq1 : 0 < q - 1 := by omega
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq1R : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hlogd : 0 ≤ Real.logb q (d : ℝ) := Real.logb_nonneg hqR hdR
  -- shorten to length `m`, the largest with `(q - 1) m < q d`
  set m := (q * d - 1) / (q - 1)
  have hqd : 0 < q * d := Nat.mul_pos (by omega) hd0
  have hm1 : (q - 1) * m ≤ q * d - 1 := Nat.mul_div_le _ _
  have hm2 : q * d - 1 < (q - 1) * (m + 1) := Nat.lt_mul_div_succ _ hq1
  have hmn : m ≤ n := by
    by_contra hlt
    have : (q - 1) * n < (q - 1) * m := Nat.mul_lt_mul_of_pos_left (by omega) hq1
    omega
  have hgap : 1 ≤ q * d - (q - 1) * m := by omega
  have hs := card_mul_sub_le_pow_mul_of_le_minDist hd hmn
  have hC : #C ≤ q ^ (n - m) * (q * d) := (Nat.le_mul_of_pos_right _ hgap).trans hs
  -- `(q - 1) (m + 1) ≥ q d` over the reals
  have hmR : (q : ℝ) * d ≤ ((q : ℝ) - 1) * (m + 1) := by
    have : q * d ≤ (q - 1) * (m + 1) := by omega
    have h' : ((q * d : ℕ) : ℝ) ≤ (((q - 1) * (m + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at h'
    exact h'
  have hdiv : (q : ℝ) * d / ((q : ℝ) - 1) ≤ m + 1 := by
    rw [div_le_iff₀ hq1R]
    linarith
  rcases Nat.eq_zero_or_pos #C with h0 | h0
  · rw [h0, Nat.cast_zero, Real.logb_zero]
    have : (q : ℝ) * d / ((q : ℝ) - 1) ≤ n := by
      rw [div_le_iff₀ hq1R]
      have h' : ((q * d : ℕ) : ℝ) ≤ (((q - 1) * n : ℕ) : ℝ) := by exact_mod_cast h
      push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at h'
      linarith
    linarith
  have hlog : Real.logb q (#C : ℝ) ≤ (n - m : ℕ) + (1 + Real.logb q (d : ℝ)) := by
    have hCR : (#C : ℝ) ≤ (q : ℝ) ^ (n - m) * (q * d) := by exact_mod_cast hC
    calc Real.logb q (#C : ℝ) ≤ Real.logb q ((q : ℝ) ^ (n - m) * (q * d)) :=
          Real.logb_le_logb_of_le hqR (by exact_mod_cast h0) hCR
      _ = (n - m : ℕ) + (1 + Real.logb q (d : ℝ)) := by
          rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
            Real.logb_mul (by positivity) (by positivity), Real.logb_self_eq_one hqR, mul_one]
  rw [Nat.cast_sub hmn] at hlog
  linarith

omit [Fintype ι] in
/-- **The asymptotic Plotkin bound** [GuruswamiRudraSudan2019, Corollary 4.4.2]. Let `C s` be codes
over `q ≥ 2` letters whose lengths `n_s` tend to infinity along a filter `l`, with relative
distance at least `δ`, where `0 ≤ δ ≤ 1 - 1 / q`: distinct codewords of `C s` differ on at least
`δ n_s` coordinates. Then for every `ε > 0`, eventually `log_q |C s| ≤ (1 - q δ / (q - 1) + ε) n_s`;
that is, the rate is at most `1 - q δ / (q - 1) + o(1)`. -/
theorem eventually_logb_card_le_of_le_hammingDist {σ : Type*} {ιs : σ → Type*}
    [∀ s, Fintype (ιs s)] [Nontrivial α] {l : Filter σ} {C : ∀ s, Finset (ιs s → α)} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : Fintype.card α * δ ≤ Fintype.card α - 1)
    (hC : ∀ s, ∀ x ∈ C s, ∀ y ∈ C s, x ≠ y → δ * Fintype.card (ιs s) ≤ hammingDist x y)
    (hn : Filter.Tendsto (fun s => Fintype.card (ιs s)) l Filter.atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in l, Real.logb (Fintype.card α) #(C s) ≤
      (1 - Fintype.card α / (Fintype.card α - 1) * δ + ε) * Fintype.card (ιs s) := by
  classical
  set q := Fintype.card α
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq1R : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hnR : Filter.Tendsto (fun s => (Fintype.card (ιs s) : ℝ)) l Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  -- the trivial bound `|C| ≤ q ^ n`
  have htriv (s : σ) : Real.logb q #(C s) ≤ Fintype.card (ιs s) := by
    rcases Nat.eq_zero_or_pos #(C s) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.logb_zero]
      positivity
    have hle : (#(C s) : ℝ) ≤ (q : ℝ) ^ Fintype.card (ιs s) := by
      have := card_le_univ (C s)
      rw [Fintype.card_fun] at this
      exact_mod_cast this
    calc Real.logb q #(C s) ≤ Real.logb q ((q : ℝ) ^ Fintype.card (ιs s)) :=
          Real.logb_le_logb_of_le hqR (by exact_mod_cast h0) hle
      _ = Fintype.card (ιs s) := by rw [Real.logb_pow, Real.logb_self_eq_one hqR, mul_one]
  rcases hδ0.eq_or_lt with rfl | hδpos
  · refine Filter.Eventually.of_forall fun s => (htriv s).trans ?_
    have : (0 : ℝ) ≤ Fintype.card (ιs s) := by positivity
    nlinarith
  -- eventually `δ n ≥ 1`, `4 ≤ ε n / 2` and `log_q n ≤ ε n / 2`
  have h1 : ∀ᶠ s in l, 1 / δ + 8 / ε ≤ (Fintype.card (ιs s) : ℝ) :=
    hnR.eventually_ge_atTop _
  have h2 : ∀ᶠ s in l, Real.log (Fintype.card (ιs s)) ≤
      ε * Real.log q / 2 * Fintype.card (ιs s) := by
    have hlogq : 0 < Real.log q := Real.log_pos hqR
    have := (Real.isLittleO_log_id_atTop.bound (c := ε * Real.log q / 2) (by positivity))
    filter_upwards [hnR.eventually this, hnR.eventually_ge_atTop 1] with s hs hs1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (Real.log_nonneg hs1),
      abs_of_nonneg (by linarith)] at hs
    exact hs
  filter_upwards [h1, h2] with s hs1 hs2
  set n := Fintype.card (ιs s)
  set d := ⌊δ * n⌋₊
  have h8ε : 0 ≤ 8 / ε := by positivity
  have h1δ : 0 < 1 / δ := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hδn : 1 ≤ δ * n := by
    have : 1 / δ ≤ n := by linarith
    rw [div_le_iff₀ hδpos] at this
    linarith
  have hd0 : 0 < d := Nat.floor_pos.2 hδn
  have hdle : (d : ℝ) ≤ δ * n := Nat.floor_le (by positivity)
  have hdgt : δ * n < d + 1 := Nat.lt_floor_add_one _
  have hdmin : (d : ℕ∞) ≤ minDist ((C s : Finset (ιs s → α)) : Set (ιs s → α)) := by
    rw [le_minDist_iff]
    intro x hx y hy hxy
    have := hC s x hx y hy hxy
    exact_mod_cast Nat.floor_le_of_le (R := ℝ) this
  have hqd : q * d ≤ (q - 1) * n := by
    have : ((q * d : ℕ) : ℝ) ≤ (((q - 1) * n : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
      calc (q : ℝ) * d ≤ q * (δ * n) := by gcongr
        _ = (q * δ) * n := by ring
        _ ≤ ((q : ℝ) - 1) * n := by gcongr
    exact_mod_cast this
  have hmain := logb_card_le_of_le_minDist hdmin hd0 hqd
  have hlogd : Real.logb q (d : ℝ) ≤ ε / 2 * n := by
    have hdn : (d : ℝ) ≤ n := by
      have : δ ≤ 1 := by
        have : (q : ℝ) * δ ≤ q := by linarith
        nlinarith
      nlinarith
    calc Real.logb q (d : ℝ) ≤ Real.logb q (n : ℝ) :=
          Real.logb_le_logb_of_le hqR (by exact_mod_cast hd0) hdn
      _ = Real.log n / Real.log q := rfl
      _ ≤ ε / 2 * n := by
          rw [div_le_iff₀ (Real.log_pos hqR)]
          linarith
  -- `q d / (q - 1) ≥ q δ n / (q - 1) - 2`
  have hqd' : (q : ℝ) / (q - 1) * δ * n - 2 ≤ (q : ℝ) * d / (q - 1) := by
    have h2q : (q : ℝ) / (q - 1) ≤ 2 := by
      rw [div_le_iff₀ hq1R]
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    have : (q : ℝ) / (q - 1) * δ * n - (q : ℝ) * d / (q - 1) =
        (q : ℝ) / (q - 1) * (δ * n - d) := by
      ring
    have hq0 : (0 : ℝ) ≤ (q : ℝ) / (q - 1) := by positivity
    nlinarith
  have h8 : 4 ≤ ε / 2 * n := by
    have : 8 / ε ≤ n := by linarith
    rw [div_le_iff₀ hε] at this
    linarith
  nlinarith

end Cslib.Code
