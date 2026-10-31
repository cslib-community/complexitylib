/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Preloss
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Charging a first overflow to errors at light targets

At the first group whose compression threshold exceeds its floor, sufficiently many real entries
exceed that floor: the preceding default is too small to cause the overflow. If fewer than half
as many true endpoints are heavy, at least half the overflowing entries are light. At each light
endpoint, a large input and small preceding compression loss force a large raw-prefix error.

This module proves the deterministic counting and charging assertion of
[OpenAI2026LogSpace, Section 8.4, (8.12)]. For a floor `0 < ρ ≤ 1`, a true first coordinate in
`[0, ρ / 4]`, a zero true second coordinate, and preloss at most `ρ / 100`, an input of size
greater than `ρ` has clipped error at least `ρ / 2`. Thus a false-type overflow satisfies
`1 ≤ 2 ^ (p + 1) / (n * ρ ^ p) * ∑ y, error y ^ p`, for every natural moment exponent `p`.

The final theorem applies this to the actual iterated compression with the explicit dyadic
floors and zero initial default. It derives the previous-default and preloss bounds from the
absence of earlier overflow. The error is taken from the uncompressed prefix at `j + 1`, not
from the compressed row. The first-overflow index is also proved unique.

This is the pointwise false-overflow charge. Conditional rarity of true heavy counts, stability
after overflow, and the integrated compression theorem remain separate obligations.

## Main results

* `Cslib.RowCompression.IsFirstOverflow.unique`: first-overflow events are disjoint.
* `Cslib.RowCompression.half_floor_le_clippedError`: a large light entry forces raw-prefix error.
* `Cslib.RowCompression.one_le_sum_clippedError_pow_of_overflow`: the explicit moment charge.
* `Cslib.RowCompression.one_le_sum_clippedError_pow_of_firstOverflow_dyadic`: the charge for the
  actual compression recursion, with numerical floor conditions discharged.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, equation labelled `buf-false-charge`
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset

variable {ι : Type*}

/-- Group `j` is the first whose actual threshold exceeds its prescribed floor. -/
@[expose] def IsFirstOverflow (s : Finset ι) (n K : ℕ → ℕ) (ρ : ℕ → ℝ)
    (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (j : ℕ) : Prop :=
  (∀ i < j, stepThreshold s n K ρ Δ a i ≤ ρ i) ∧ ρ j < stepThreshold s n K ρ Δ a j

/-- A run cannot have two different first-overflow groups. -/
theorem IsFirstOverflow.unique {s : Finset ι} {n K : ℕ → ℕ} {ρ : ℕ → ℝ}
    {Δ : ℕ → ι → Fin 2 → ℝ} {a : State ι} {j k : ℕ}
    (hj : IsFirstOverflow s n K ρ Δ a j) (hk : IsFirstOverflow s n K ρ Δ a k) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact False.elim (not_lt_of_ge (hk.1 j h) hj.2)
  · exact h
  · exact False.elim (not_lt_of_ge (hj.1 k h) hk.2)

/-- A light true target cannot produce a large compression input without a large raw error.
Both input channels may have either sign. -/
theorem half_floor_le_clippedError {ρ d v : ℝ} {w raw : Fin 2 → ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hd : 0 ≤ d) (hdρ : d ≤ ρ / 4) (hv : v = 0)
    (hprev : ∀ ν, |w ν - raw ν| ≤ ρ / 100) (hsize : ρ < entrySize w) :
    ρ / 2 ≤ clippedError d v raw := by
  have hsmall : ρ / 2 ≤ 1 := by linarith
  rcases lt_max_iff.mp hsize with hfirst | hsecond
  · have hraw : |w 0| ≤ ρ / 100 + (|raw 0 - d| + d) := by
      calc
        _ ≤ |w 0 - raw 0| + |raw 0| := by
          simpa only [sub_zero] using abs_sub_le (w 0) (raw 0) 0
        _ ≤ ρ / 100 + (|raw 0 - d| + d) := by
          apply add_le_add (hprev 0)
          simpa only [sub_zero, abs_of_nonneg hd] using abs_sub_le (raw 0) d 0
    have hden : 0 < 1 + d := by linarith
    have hrel : ρ / 2 ≤ |raw 0 - d| / (1 + d) := by
      apply (le_div_iff₀ hden).2
      calc
        _ ≤ (ρ / 2) * (5 / 4) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ _ := by linarith
    exact (le_min hsmall hrel).trans (le_max_left _ _)
  · have hraw : |w 1| ≤ ρ / 100 + |raw 1| := by
      have h : |w 1| ≤ |w 1 - raw 1| + |raw 1| := by
        simpa only [sub_zero] using abs_sub_le (w 1) (raw 1) 0
      exact h.trans (add_le_add (hprev 1) le_rfl)
    have hrel : ρ / 2 ≤ |raw 1 - v| := by rw [hv, sub_zero]; linarith
    exact (le_min hsmall hrel).trans (le_max_right _ _)

/-- If the old default is below the floor, an overflow needs at least `n` real large entries. -/
theorem le_card_large_of_overflow {s : Finset ι} {n : ℕ} {ρ z : ℝ}
    {w : ι → Fin 2 → ℝ} (hn : 0 < n) (hρ : 0 ≤ ρ) (hz : z ≤ ρ)
    (hover : ρ < threshold s n ρ z w) :
    n ≤ #{y ∈ s | ρ < entrySize (w y)} := by
  apply (lt_kthLargest_iff hn hρ).mp
  unfold threshold at hover
  rcases lt_max_iff.mp hover with h | h
  · exact False.elim (not_lt_of_ge hz h)
  · simpa only [lt_max_iff, lt_self_iff_false, false_or] using h

/-- The moment sum pays for an overflow unless at least half its capacity is truly heavy.
The constant is explicit, and the bound allows arbitrary dependence between entries. -/
theorem one_le_sum_clippedError_pow_of_overflow {s : Finset ι} {n : ℕ} {ρ z : ℝ}
    {w raw truth : ι → Fin 2 → ℝ} (hn : 0 < n) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hz : z ≤ ρ) (hover : ρ < threshold s n ρ z w)
    (hfirst : ∀ y ∈ s, 0 ≤ truth y 0)
    (hsecond : ∀ y ∈ s, truth y 0 ≤ ρ / 4 → truth y 1 = 0)
    (hprev : ∀ y ∈ s, ∀ ν, |w y ν - raw y ν| ≤ ρ / 100)
    (hheavy : 2 * #{y ∈ s | ρ / 4 < truth y 0} < n) (p : ℕ) :
    1 ≤ (2 : ℝ) ^ (p + 1) / ((n : ℝ) * ρ ^ p) *
      ∑ y ∈ s, clippedError (truth y 0) (truth y 1) (raw y) ^ p := by
  classical
  let large := {y ∈ s | ρ < entrySize (w y)}
  let heavy := {y ∈ s | ρ / 4 < truth y 0}
  let light := {y ∈ large | truth y 0 ≤ ρ / 4}
  have hnlarge : n ≤ #large := le_card_large_of_overflow hn hρ.le hz hover
  have hcover : large ⊆ light ∪ heavy := by
    intro y hy
    by_cases hd : truth y 0 ≤ ρ / 4
    · exact mem_union_left _ (mem_filter.mpr ⟨hy, hd⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨(mem_filter.mp hy).1, lt_of_not_ge hd⟩)
  have hcount : n ≤ 2 * #light := by
    have hcard := (card_le_card hcover).trans (card_union_le light heavy)
    change 2 * #heavy < n at hheavy
    omega
  have hhalf : (n : ℝ) / 2 ≤ #light := by
    have hc : (n : ℝ) ≤ 2 * (#light : ℝ) := by exact_mod_cast hcount
    linarith
  have hsubset : light ⊆ s := fun _ hy => (mem_filter.mp (mem_filter.mp hy).1).1
  have hsum : (#light : ℝ) * (ρ / 2) ^ p ≤
      ∑ y ∈ s, clippedError (truth y 0) (truth y 1) (raw y) ^ p := by
    calc
      _ = ∑ _y ∈ light, (ρ / 2) ^ p := by simp
      _ ≤ ∑ y ∈ light, clippedError (truth y 0) (truth y 1) (raw y) ^ p := by
        apply sum_le_sum
        intro y hy
        have hys := hsubset hy
        exact pow_le_pow_left₀ (by positivity) (half_floor_le_clippedError hρ hρ1
          (hfirst y hys) (mem_filter.mp hy).2 (hsecond y hys (mem_filter.mp hy).2)
          (hprev y hys) (mem_filter.mp (mem_filter.mp hy).1).2) p
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsubset fun y _ _ =>
        pow_nonneg (clippedError_nonneg _ _ _) _
  have hcharge := (mul_le_mul_of_nonneg_right hhalf
    (pow_nonneg (by positivity : 0 ≤ ρ / 2) p)).trans hsum
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) / 2 * (ρ / 2) ^ p := by positivity
  calc
    1 ≤ (∑ y ∈ s, clippedError (truth y 0) (truth y 1) (raw y) ^ p) /
        ((n : ℝ) / 2 * (ρ / 2) ^ p) := (le_div_iff₀ hden).2 (by simpa using hcharge)
    _ = _ := by
      rw [div_pow, pow_succ]
      field_simp

/-- The false-overflow charge for the actual dyadic compression run. Earlier non-overflow and
the explicit floor separation imply all default and preloss hypotheses of the local charge. -/
theorem one_le_sum_clippedError_pow_of_firstOverflow_dyadic {s : Finset ι}
    {n K : ℕ → ℕ} {Δ : ℕ → ι → Fin 2 → ℝ} {a : State ι} {truth : ι → Fin 2 → ℝ}
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (ha : a.defaultValue = 0)
    (m j : ℕ) (hj : j < m) (hn : 0 < n j)
    (hover : IsFirstOverflow s n K (dyadicFloor η m) Δ a j)
    (hfirst : ∀ y ∈ s, 0 ≤ truth y 0)
    (hsecond : ∀ y ∈ s, truth y 0 ≤ dyadicFloor η m j / 4 → truth y 1 = 0)
    (hheavy : 2 * #{y ∈ s | dyadicFloor η m j / 4 < truth y 0} < n j) (p : ℕ) :
    1 ≤ (2 : ℝ) ^ (p + 1) / ((n j : ℝ) * dyadicFloor η m j ^ p) *
      ∑ y ∈ s, clippedError (truth y 0) (truth y 1)
        (uncompressedRow Δ a.row (j + 1) y) ^ p := by
  have hρ := dyadicFloor_pos hη m j
  have hρ1 : dyadicFloor η m j ≤ 1 := by
    have h := dyadicFloor_le_scale_div hη.le m j
    linarith
  have hsum := six_sum_range_dyadicFloor_le hη.le hj
  have hzabs := abs_iterate_defaultValue_sub_le_of_no_overflow
    (show 0 ≤ a.defaultValue by rw [ha]) j hover.1
  rw [ha, sub_zero] at hzabs
  have hz : (iterate s n K (dyadicFloor η m) Δ a j).defaultValue ≤ dyadicFloor η m j := by
    have h := le_abs_self (iterate s n K (dyadicFloor η m) Δ a j).defaultValue
    linarith
  apply one_le_sum_clippedError_pow_of_overflow hn hρ hρ1 hz hover.2 hfirst hsecond ?_ hheavy p
  intro y _ ν
  rw [uncompressedRow_succ]
  simp only [inputRow, Pi.add_apply, add_sub_add_right_eq_sub]
  exact (abs_iterate_sub_uncompressed_le_of_no_overflow j hover.1 y ν).trans hsum

end Cslib.RowCompression
