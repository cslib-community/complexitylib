/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.CorrectionAtom
import Complexity.Foundations.Data.Finset.Markov
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conditional rarity of retained heavy entries

A row on a finite endpoint set `S` has first signal `d` and bounded mass
`a * ∑ w ∈ S, d w ≤ M`. At a floor `ρ > 0`, its heavy-set cardinality satisfies
`#{w ∈ S | ρ / 4 < d w} * a * ρ ≤ 4 * M`, including at zero scale `a = 0`.
Suppose that, on a finite slice of draws, every heavy endpoint other than one specified
endpoint is retained on at most a
`c * a` fraction of the draws. The specified endpoint can contribute one retained entry.
Markov's inequality then bounds the fraction of draws retaining at least `n / 2` heavy
entries by `2 * (1 + 4 * c * M) / (n * ρ)` when `ρ ≤ 1`.

The slice is arbitrary: it may condition on a narrower endpoint channel and a start channel,
provided its explicit pair bound holds. No independence among the heavy-entry hits is required.
The division-free estimate also permits an empty slice or zero capacity. This is the counting
part of [OpenAI2026LogSpace, Lemma 8.4]; weighting deterministic mean errors and the complete
integrated compression bound are separate steps.

## Main definitions

* `Cslib.Probability.heavyCountEvent`: at least half the capacity is truly heavy and retained.

## Main results

* `Cslib.Probability.card_filter_heavy_mul_le`: the deterministic heavy-set mass bound.
* `Cslib.Probability.card_filter_heavyCountEvent_mul_le`: rarity without division.
* `Cslib.Probability.card_filter_heavyCountEvent_le`: the explicit conditional rarity factor.
* `Cslib.Probability.card_filter_heavyCountEvent_div_card_le`: the conditional frequency bound,
  including empty slices.
* `Cslib.Probability.card_filter_heavyCountEvent_product_div_card_le`: an independent start
  slice preserves the frequency bound.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, Lemma 8.4, equation (8.13) on p. 48 (source label `buf-rarity`)
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Probability

variable {Ω V : Type*}

open Classical in
/-- A true heavy count at floor `ρ`: at least half the capacity `n` consists of retained
endpoints in `S` whose deterministic first signal exceeds `ρ / 4`. -/
@[expose] def heavyCountEvent (Y : Ω → V → Prop) (S : Finset V) (d : V → ℝ) (ρ : ℝ) (n : ℕ)
    (σ : Ω) : Prop :=
  n ≤ 2 * #{w ∈ S | Y σ w ∧ ρ / 4 < d w}

/-- The deterministic mass bounds the number of entries above a quarter of the floor.
The multiplied form remains valid at zero scale and for every floor. -/
theorem card_filter_heavy_mul_le (S : Finset V) {a ρ M : ℝ} {d : V → ℝ} (ha : 0 ≤ a)
    (hd : ∀ w ∈ S, 0 ≤ d w) (hmass : a * ∑ w ∈ S, d w ≤ M) :
    (#{w ∈ S | ρ / 4 < d w} : ℝ) * (a * ρ) ≤ 4 * M := by
  classical
  have hcount : (#{w ∈ S | ρ / 4 < d w} : ℝ) * (ρ / 4) ≤ ∑ w ∈ S, d w :=
    card_filter_mul_le_sum S _ d hd fun _ _ hw => hw.le
  have h := (mul_le_mul_of_nonneg_left hcount ha).trans hmass
  linarith

open Classical in
/-- Conditional rarity of a true heavy count, without division. The endpoint `y` may be
forced by the conditioning slice, while only the other heavy endpoints need its pair-count bound.
The slice and the capacity may be empty or zero. -/
theorem card_filter_heavyCountEvent_mul_le (Y : Ω → V → Prop) (T : Finset Ω)
    (S : Finset V) (y : V) {d : V → ℝ} {a ρ c M : ℝ}
    (ha : 0 ≤ a) (hρ : 0 < ρ) (hc : 0 ≤ c)
    (hd : ∀ w ∈ S, 0 ≤ d w) (hmass : a * ∑ w ∈ S, d w ≤ M)
    (hpair : ∀ w ∈ S, ρ / 4 < d w → w ≠ y →
      (#{σ ∈ T | Y σ w} : ℝ) ≤ c * a * #T) (n : ℕ) :
    (#{σ ∈ T | heavyCountEvent Y S d ρ n σ} : ℝ) * n * ρ ≤
      #T * (2 * (ρ + 4 * c * M)) := by
  classical
  let D : Finset V := {w ∈ S | ρ / 4 < d w}
  have hfilter (σ : Ω) : ({w ∈ D | Y σ w} : Finset V) =
      ({w ∈ S | Y σ w ∧ ρ / 4 < d w} : Finset V) := by
    ext w
    simp [D, and_left_comm, and_comm]
  have hevent (σ : Ω) : (n + 1) / 2 ≤ #{w ∈ D | Y σ w} ↔
      heavyCountEvent Y S d ρ n σ := by
    rw [hfilter]
    unfold heavyCountEvent
    omega
  have hcount := card_filter_le_card_filter_mul_le Y T D y (mul_nonneg hc ha)
    (fun w hw hwy => hpair w (mem_filter.mp hw).1 (mem_filter.mp hw).2 hwy) ((n + 1) / 2)
  simp only [hevent] at hcount
  have hn : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * ((n + 1) / 2) by omega)
  have hmassD : (#D : ℝ) * (a * ρ) ≤ 4 * M :=
    card_filter_heavy_mul_le S ha hd hmass
  have hmassc : c * a * #D * ρ ≤ 4 * c * M := by
    have h := mul_le_mul_of_nonneg_left hmassD hc
    nlinarith
  calc
    _ ≤ (#{σ ∈ T | heavyCountEvent Y S d ρ n σ} : ℝ) *
        (2 * (((n + 1) / 2 : ℕ) : ℝ)) * ρ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by positivity)) hρ.le
    _ = 2 * ((#{σ ∈ T | heavyCountEvent Y S d ρ n σ} : ℝ) *
        (((n + 1) / 2 : ℕ) : ℝ)) * ρ := by ring
    _ ≤ 2 * (#T * (1 + c * a * #D)) * ρ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount (by norm_num)) hρ.le
    _ = #T * (2 * (ρ + c * a * #D * ρ)) := by ring
    _ ≤ #T * (2 * (ρ + 4 * c * M)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hmassc) (by norm_num)) (by positivity)

open Classical in
/-- The conditional rarity factor `2 * (1 + 4 * c * M) / (n * ρ)` for a positive capacity
and a floor in `(0, 1]`. Empty slices require no special convention. -/
theorem card_filter_heavyCountEvent_le (Y : Ω → V → Prop) (T : Finset Ω)
    (S : Finset V) (y : V) {d : V → ℝ} {a ρ c M : ℝ}
    (ha : 0 ≤ a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hc : 0 ≤ c) (hd : ∀ w ∈ S, 0 ≤ d w) (hmass : a * ∑ w ∈ S, d w ≤ M)
    (hpair : ∀ w ∈ S, ρ / 4 < d w → w ≠ y →
      (#{σ ∈ T | Y σ w} : ℝ) ≤ c * a * #T)
    {n : ℕ} (hn : 0 < n) :
    (#{σ ∈ T | heavyCountEvent Y S d ρ n σ} : ℝ) ≤
      (2 * (1 + 4 * c * M) / ((n : ℝ) * ρ)) * #T := by
  classical
  have h := card_filter_heavyCountEvent_mul_le Y T S y ha hρ hc hd hmass hpair n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hn' hρ)]
  calc
    _ = (#{σ ∈ T | heavyCountEvent Y S d ρ n σ} : ℝ) * n * ρ := by ring
    _ ≤ #T * (2 * (ρ + 4 * c * M)) := h
    _ ≤ #T * (2 * (1 + 4 * c * M)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add hρ1 le_rfl) (by norm_num)) (by positivity)
    _ = _ := by ring

open Classical in
/-- The conditional true-heavy-count frequency bound. An empty conditioning slice has
frequency zero, so no nonemptiness hypothesis is needed. -/
theorem card_filter_heavyCountEvent_div_card_le (Y : Ω → V → Prop) (T : Finset Ω)
    (S : Finset V) (y : V) {d : V → ℝ} {a ρ c M : ℝ}
    (ha : 0 ≤ a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 ≤ c)
    (hd : ∀ w ∈ S, 0 ≤ d w) (hmass : a * ∑ w ∈ S, d w ≤ M)
    (hpair : ∀ w ∈ S, ρ / 4 < d w → w ≠ y →
      (#{σ ∈ T | Y σ w} : ℝ) ≤ c * a * #T) {n : ℕ} (hn : 0 < n) :
    (#{σ ∈ T | heavyCountEvent Y S d ρ n σ} : ℝ) / #T ≤
      2 * (1 + 4 * c * M) / ((n : ℝ) * ρ) := by
  classical
  have hM : 0 ≤ M := (mul_nonneg ha (sum_nonneg hd)).trans hmass
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp only [filter_empty, card_empty, Nat.cast_zero, zero_div]
    positivity
  have hTpos : (0 : ℝ) < #T := by exact_mod_cast hT.card_pos
  exact (div_le_iff₀ hTpos).mpr
    (card_filter_heavyCountEvent_le Y T S y ha hρ hρ1 hc hd hmass hpair hn)

open Classical in
/-- Conditioning independently on a start seed preserves the heavy-count frequency bound.
The actual product slice is used, and either of its two factors may be empty. -/
theorem card_filter_heavyCountEvent_product_div_card_le {Γ : Type*}
    (Y : Ω → V → Prop) (R : Finset Γ) (T : Finset Ω) (S : Finset V) (y : V)
    {d : V → ℝ} {a ρ c M : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 ≤ c)
    (hd : ∀ w ∈ S, 0 ≤ d w) (hmass : a * ∑ w ∈ S, d w ≤ M)
    (hpair : ∀ w ∈ S, ρ / 4 < d w → w ≠ y →
      (#{σ ∈ T | Y σ w} : ℝ) ≤ c * a * #T) {n : ℕ} (hn : 0 < n) :
    (#{σ ∈ R ×ˢ T | heavyCountEvent (fun σ w => Y σ.2 w) S d ρ n σ} : ℝ) / #(R ×ˢ T) ≤
      2 * (1 + 4 * c * M) / ((n : ℝ) * ρ) := by
  classical
  refine card_filter_heavyCountEvent_div_card_le (fun (σ : Γ × Ω) w => Y σ.2 w)
    (R ×ˢ T) S y ha hρ hρ1 hc hd hmass ?_ hn
  intro w hw hdw hwy
  have hset : {σ ∈ R ×ˢ T | Y σ.2 w} = R ×ˢ {σ ∈ T | Y σ w} := by
    ext σ
    simp [and_assoc]
  rw [hset, card_product, card_product, Nat.cast_mul, Nat.cast_mul]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left (hpair w hw hdw hwy) (Nat.cast_nonneg #R : (0 : ℝ) ≤ #R)

end Cslib.Probability
