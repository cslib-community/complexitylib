/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.StochasticAtom
import Mathlib.Tactic.Linarith

/-!
# Sparse support of separated stochastic bins

At most two adjacent bins can be active at a fixed entry when successive scales shrink
by a factor of at least two. This is an original finite consequence of the bin support API.

## Main results

* `Cslib.card_filter_binWeight_ne_zero_le_two`: a width-independent support count.
-/
public section
namespace Cslib
open Finset
variable {χ : ℝ → ℝ} {b : ℕ → ℝ}
/-- With adjacent scales separated by at least two, at most two bins are nonzero at
any entry. This includes the top bin and requires no positive lower bound on the entry. -/
theorem card_filter_binWeight_ne_zero_le_two
    (hχ0 : ∀ t, t ≤ 1 / 2 → χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1)
    (hb : ∀ k, 0 < b k) (hanti : Antitone b)
    (hstep : ∀ k, 2 * b (k + 1) ≤ b k) (I : Finset ℕ) (w : ℝ) :
    #{i ∈ I | binWeight χ b i w ≠ 0} ≤ 2 := by
  classical
  let S := I.filter fun i => binWeight χ b i w ≠ 0
  change #S ≤ 2
  rcases S.eq_empty_or_nonempty with hs | hs
  · simp [hs]
  let a := S.min' hs
  have ha : binWeight χ b a w ≠ 0 := (mem_filter.mp (min'_mem S hs)).2
  have hlo : b a / 2 < w := by
    cases he : a with
    | zero =>
      by_contra h
      apply ha
      rw [he, binWeight, hχ0 _ ((div_le_iff₀ (hb 0)).mpr (by linarith [not_lt.mp h]))]
    | succ a => exact (binWeight_succ_ne_zero hχ0 hχ1 hb hanti (he ▸ ha)).1
  apply (card_le_card (show S ⊆ {a, a + 1} from ?_)).trans card_le_two
  intro i hi
  have hai : a ≤ i := min'_le S i hi
  have hupper : i ≤ a + 1 := by
    by_contra h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    have hw := (binWeight_succ_ne_zero hχ0 hχ1 hb hanti (mem_filter.mp hi).2).2
    have hbj := hanti (show a + 1 ≤ j by omega)
    linarith [hstep a]
  simp only [mem_insert, mem_singleton]
  omega

end Cslib
