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

A row with first signal `d` has bounded mass `a * ∑ w, d w ≤ M`. At a floor `ρ > 0`,
there are at most `4 * M / (a * ρ)` entries above `ρ / 4`. Suppose that, on a finite slice
of draws, every endpoint other than one specified endpoint is retained on at most a
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

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, Lemma 8.4, equation labelled `buf-rarity`
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Probability

variable {Ω V : Type*} [Fintype V]

open Classical in
/-- A true heavy count at floor `ρ`: at least half the capacity `n` consists of retained
endpoints whose deterministic first signal exceeds `ρ / 4`. -/
@[expose] def heavyCountEvent (Y : Ω → V → Prop) (d : V → ℝ) (ρ : ℝ) (n : ℕ)
    (σ : Ω) : Prop :=
  n ≤ 2 * #{w | Y σ w ∧ ρ / 4 < d w}

/-- The deterministic mass bounds the number of entries above a quarter of the floor.
The multiplied form remains valid at zero scale and for every floor. -/
theorem card_filter_heavy_mul_le {a ρ M : ℝ} {d : V → ℝ} (ha : 0 ≤ a)
    (hd : ∀ w, 0 ≤ d w) (hmass : a * ∑ w, d w ≤ M) :
    (#{w | ρ / 4 < d w} : ℝ) * (a * ρ) ≤ 4 * M := by
  classical
  have hcount : (#{w | ρ / 4 < d w} : ℝ) * (ρ / 4) ≤ ∑ w, d w :=
    card_filter_mul_le_sum univ _ d (fun w _ => hd w) fun _ _ hw => hw.le
  have h := (mul_le_mul_of_nonneg_left hcount ha).trans hmass
  linarith

open Classical in
/-- Conditional rarity of a true heavy count, without division. The endpoint `y` may be
forced by the conditioning slice, while all other endpoints satisfy its pair-count bound.
The slice and the capacity may be empty or zero. -/
theorem card_filter_heavyCountEvent_mul_le (Y : Ω → V → Prop) (T : Finset Ω) (y : V)
    {d : V → ℝ} {a ρ c M : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hc : 0 ≤ c)
    (hd : ∀ w, 0 ≤ d w) (hmass : a * ∑ w, d w ≤ M)
    (hpair : ∀ w, w ≠ y → (#{σ ∈ T | Y σ w} : ℝ) ≤ c * a * #T) (n : ℕ) :
    (#{σ ∈ T | heavyCountEvent Y d ρ n σ} : ℝ) * n * ρ ≤
      #T * (2 * (ρ + 4 * c * M)) := by
  classical
  let D : Finset V := {w | ρ / 4 < d w}
  have hfilter (σ : Ω) : ({w ∈ D | Y σ w} : Finset V) =
      ({w | Y σ w ∧ ρ / 4 < d w} : Finset V) := by
    ext w
    simp [D, and_comm]
  have hevent (σ : Ω) : (n + 1) / 2 ≤ #{w ∈ D | Y σ w} ↔
      heavyCountEvent Y d ρ n σ := by
    rw [hfilter]
    unfold heavyCountEvent
    omega
  have hcount := card_filter_le_card_filter_mul_le Y T D y (mul_nonneg hc ha.le)
    (fun w _ hw => hpair w hw) ((n + 1) / 2)
  simp only [hevent] at hcount
  have hn : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * ((n + 1) / 2) by omega)
  have hmassD : (#D : ℝ) * (a * ρ) ≤ 4 * M :=
    card_filter_heavy_mul_le ha.le hd hmass
  have hmassc : c * a * #D * ρ ≤ 4 * c * M := by
    have h := mul_le_mul_of_nonneg_left hmassD hc
    nlinarith
  calc
    _ ≤ (#{σ ∈ T | heavyCountEvent Y d ρ n σ} : ℝ) *
        (2 * (((n + 1) / 2 : ℕ) : ℝ)) * ρ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by positivity)) hρ.le
    _ = 2 * ((#{σ ∈ T | heavyCountEvent Y d ρ n σ} : ℝ) *
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
theorem card_filter_heavyCountEvent_le (Y : Ω → V → Prop) (T : Finset Ω) (y : V)
    {d : V → ℝ} {a ρ c M : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hc : 0 ≤ c) (hd : ∀ w, 0 ≤ d w) (hmass : a * ∑ w, d w ≤ M)
    (hpair : ∀ w, w ≠ y → (#{σ ∈ T | Y σ w} : ℝ) ≤ c * a * #T)
    {n : ℕ} (hn : 0 < n) :
    (#{σ ∈ T | heavyCountEvent Y d ρ n σ} : ℝ) ≤
      (2 * (1 + 4 * c * M) / ((n : ℝ) * ρ)) * #T := by
  classical
  have h := card_filter_heavyCountEvent_mul_le Y T y ha hρ hc hd hmass hpair n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hn' hρ)]
  calc
    _ = (#{σ ∈ T | heavyCountEvent Y d ρ n σ} : ℝ) * n * ρ := by ring
    _ ≤ #T * (2 * (ρ + 4 * c * M)) := h
    _ ≤ #T * (2 * (1 + 4 * c * M)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add hρ1 le_rfl) (by norm_num)) (by positivity)
    _ = _ := by ring

end Cslib.Probability
