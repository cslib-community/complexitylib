/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HeavyCount
public import Complexity.Probability.PairwiseIndependentHash.AtomChannels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Heavy-count rarity for affine retention channels

The conditional heavy-count bound applies to the actual affine retention channels with nominal
rate `a ^ H` and box side `⌈P * a⌉`. Conditioning on a specified endpoint retained by any narrower
box of side `L_t` preserves the off-diagonal pair bound `2 ^ H * a ^ H`. Thus a nonnegative row
of nominal mass at most `M` retains at least half of a positive capacity `n` above floor `ρ / 4`
on at most a `2 * (1 + 4 * 2 ^ H * M) / (n * ρ)` fraction of these conditional draws.

The result concerns the true heavy-count event on the actual shared seed. It assumes neither
independence among retained endpoints nor a rarity hypothesis. An empty conditioning slice is
allowed. This supplies the affine-channel instance of [OpenAI2026LogSpace, Lemma 8.4].

## Main results

* `Cslib.Probability.card_heavyCountEvent_affineRetains_le`: rarity after a narrower endpoint hit.
* `Cslib.Probability.card_heavyCountEvent_affineRetains_div_card_le`: the corresponding
  conditional frequency, including empty slices.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, Lemma 8.4 (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Probability

open Classical in
/-- The true heavy count for the actual affine channel is rare even after conditioning on
a hit at a narrower rate. Its nominal row-mass scale is `a ^ H`, not the box side `a`. -/
theorem card_heavyCountEvent_affineRetains_le {V : Type*} (S : Finset V) {P H : ℕ}
    [Fact P.Prime] {ident : V → ZMod P} (hident : Function.Injective ident)
    {a : ℝ} (hPa : 1 ≤ P * a) (ha : a ≤ 1) {Lt : ℕ} (hLt : Lt ≤ ⌈P * a⌉₊)
    {d : V → ℝ} {ρ M : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hd : ∀ w ∈ S, 0 ≤ d w) (hmass : a ^ H * ∑ w ∈ S, d w ≤ M)
    {n : ℕ} (hn : 0 < n) (y : V) :
    (#{s | affineRetains P H Lt s (ident y) ∧
        heavyCountEvent (fun s w => affineRetains P H ⌈P * a⌉₊ s (ident w)) S d ρ n s} : ℝ) ≤
      (2 * (1 + 4 * (2 : ℝ) ^ H * M) / ((n : ℝ) * ρ)) *
        #{s | affineRetains P H Lt s (ident y)} := by
  classical
  have ha0 : 0 < a := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg P) (not_lt.mp h)
    linarith
  have hLtP : Lt ≤ P := hLt.trans (affineRetains_rates (H := H) hPa ha).1
  simpa only [filter_filter] using card_filter_heavyCountEvent_le
    (fun s w => affineRetains P H ⌈P * a⌉₊ s (ident w))
    ({s | affineRetains P H Lt s (ident y)} : Finset _) S y
    (pow_nonneg ha0.le H) hρ hρ1 (by positivity : 0 ≤ (2 : ℝ) ^ H) hd hmass
    (fun w _ _ hwy => by
      have h := card_affineRetains_and_affineRetains_le (H := H) hident hPa ha hLtP hwy
      convert h using 2
      congr 1
      ext s
      simp only [mem_filter, mem_univ, true_and]) hn

open Classical in
/-- The actual affine heavy-count frequency after a narrower endpoint hit. This is obtained
from the count bound above, with zero frequency when the conditioning slice is empty. -/
theorem card_heavyCountEvent_affineRetains_div_card_le {V : Type*} (S : Finset V) {P H : ℕ}
    [Fact P.Prime] {ident : V → ZMod P} (hident : Function.Injective ident)
    {a : ℝ} (hPa : 1 ≤ P * a) (ha : a ≤ 1) {Lt : ℕ} (hLt : Lt ≤ ⌈P * a⌉₊)
    {d : V → ℝ} {ρ M : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hd : ∀ w ∈ S, 0 ≤ d w) (hmass : a ^ H * ∑ w ∈ S, d w ≤ M)
    {n : ℕ} (hn : 0 < n) (y : V) :
    (#{s ∈ ({s | affineRetains P H Lt s (ident y)} :
        Finset (Matrix (Fin H) (Fin 1) (ZMod P) × (Fin H → ZMod P))) |
      heavyCountEvent (fun s w => affineRetains P H ⌈P * a⌉₊ s (ident w)) S d ρ n s} : ℝ) /
        #{s | affineRetains P H Lt s (ident y)} ≤
      2 * (1 + 4 * (2 : ℝ) ^ H * M) / ((n : ℝ) * ρ) := by
  classical
  have ha0 : 0 ≤ a := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg P) (not_le.mp h).le
    linarith
  have hM : 0 ≤ M := (mul_nonneg (pow_nonneg ha0 H) (sum_nonneg hd)).trans hmass
  let T : Finset (Matrix (Fin H) (Fin 1) (ZMod P) × (Fin H → ZMod P)) :=
    {s | affineRetains P H Lt s (ident y)}
  change (#{s ∈ T | _} : ℝ) / #T ≤ _
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT]
    simp only [filter_empty, card_empty, Nat.cast_zero, zero_div]
    positivity
  have hTpos : (0 : ℝ) < #T := by exact_mod_cast hT.card_pos
  apply (div_le_iff₀ hTpos).mpr
  simpa only [T, filter_filter] using
    card_heavyCountEvent_affineRetains_le S hident hPa ha hLt hρ hρ1 hd hmass hn y

end Cslib.Probability
