/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Log

/-!
# Binary search for the boundary of an antitone test

`lowerBoundM t lo hi` finds, by bisection, the first index of `[lo, hi)` at which a Boolean test
`t : ℕ → TimeM ℕ Bool` fails, assuming `t` holds on an initial segment of the interval and fails
on the rest. The cost of the search is the total cost of its probes; each probe is charged
whatever `t` charges, and index arithmetic is free.

## Main definitions

* `Cslib.Algorithms.Lean.lowerBoundM`: bisection on `[lo, hi)` in `TimeM ℕ`.

## Main results

* `Cslib.Algorithms.Lean.lowerBoundM_spec`: if `t` is antitone on `[lo, hi)`, the result `k`
  satisfies `lo ≤ k ≤ max lo hi`, `t` holds on `[lo, k)` and fails on `[k, hi)`.
* `Cslib.Algorithms.Lean.lowerBoundM_time_le`: if every probe costs at most `c`, the search costs
  at most `c * (Nat.log 2 (hi - lo) + 1)`; with unit-cost probes, at most `⌊log₂ (hi - lo)⌋ + 1`
  probes.
-/

public section

namespace Cslib.Algorithms.Lean

/-- Bisection for the boundary of a Boolean test on `[lo, hi)`: probe the midpoint `m` and
continue on `[m + 1, hi)` if `t m` holds and on `[lo, m)` otherwise. When `t` holds exactly on an
initial segment of `[lo, hi)`, the result is the first index where it fails (`hi` if none). -/
def lowerBoundM (t : ℕ → TimeM ℕ Bool) (lo hi : ℕ) : TimeM ℕ ℕ :=
  if h : lo < hi then do
    let b ← t ((lo + hi) / 2)
    if b then lowerBoundM t ((lo + hi) / 2 + 1) hi else lowerBoundM t lo ((lo + hi) / 2)
  else
    return lo
termination_by hi - lo
decreasing_by all_goals omega

/-- Correctness of `lowerBoundM`: if `t` is antitone on `[lo, hi)` (once it fails, it keeps
failing), then the result `k` lies in `[lo, max lo hi]`, `t` holds on `[lo, k)` and fails on
`[k, hi)`. -/
theorem lowerBoundM_spec (t : ℕ → TimeM ℕ Bool) {lo hi : ℕ}
    (hmono : ∀ m m', lo ≤ m → m ≤ m' → m' < hi → (t m').ret = true → (t m).ret = true) :
    lo ≤ (lowerBoundM t lo hi).ret ∧ (lowerBoundM t lo hi).ret ≤ max lo hi ∧
      (∀ m, lo ≤ m → m < (lowerBoundM t lo hi).ret → (t m).ret = true) ∧
      (∀ m, (lowerBoundM t lo hi).ret ≤ m → m < hi → (t m).ret = false) := by
  generalize hk : hi - lo = k
  induction k using Nat.strong_induction_on generalizing lo hi with
  | _ k ih =>
    rw [lowerBoundM]
    split_ifs with hlt
    · simp only [TimeM.ret_bind]
      set mid := (lo + hi) / 2 with hmid
      have hlm : lo ≤ mid := by omega
      have hmh : mid < hi := by omega
      cases hb : (t mid).ret
      · simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨h1, h2, h3, h4⟩ := ih (mid - lo) (by omega) (lo := lo) (hi := mid)
          (fun m m' hm hmm' hm' => hmono m m' hm hmm' (by omega)) rfl
        refine ⟨h1, by omega, h3, fun m hm hmhi => ?_⟩
        rcases Nat.lt_or_ge m mid with hlt' | hge
        · exact h4 m hm hlt'
        · cases htm : (t m).ret
          · rfl
          · have := hmono mid m hlm hge hmhi htm
            rw [hb] at this
            exact absurd this Bool.false_ne_true
      · simp only [↓reduceIte]
        obtain ⟨h1, h2, h3, h4⟩ := ih (hi - (mid + 1)) (by omega) (lo := mid + 1) (hi := hi)
          (fun m m' hm hmm' hm' => hmono m m' (by omega) hmm' hm') rfl
        refine ⟨by omega, by omega, fun m hm hmk => ?_, h4⟩
        rcases Nat.lt_or_ge m (mid + 1) with hlt' | hge
        · exact hmono m mid hm (by omega) hmh hb
        · exact h3 m hge hmk
    · simp only [TimeM.ret_pure]
      refine ⟨le_refl _, le_max_left _ _, fun m hm hm' => by omega, fun m hm hm' => by omega⟩

/-- `Nat.log 2 (2 * k') + 1 ≤ Nat.log 2 (2 * k)` when `0 < k'` and `2 * k' ≤ k`. -/
private theorem log_two_mul_add_one_le {k k' : ℕ} (hpos : 0 < k') (h2 : 2 * k' ≤ k) :
    Nat.log 2 (2 * k') + 1 ≤ Nat.log 2 (2 * k) := by
  have e1 : Nat.log 2 (2 * k') = Nat.log 2 k' + 1 := by
    rw [show 2 * k' = k' * 2 by omega]
    exact Nat.log_mul_base (b := 2) (n := k') (by omega) (by omega)
  have e2 : Nat.log 2 (k' * 2 * 2) = Nat.log 2 k' + 1 + 1 := by
    rw [Nat.log_mul_base (b := 2) (n := k' * 2) (by omega) (by omega),
      Nat.log_mul_base (b := 2) (n := k') (by omega) (by omega)]
  have := Nat.log_mono_right (b := 2) (show k' * 2 * 2 ≤ 2 * k by omega)
  omega

/-- **Cost of binary search.** If every probe costs at most `c`, then `lowerBoundM` costs at most
`c * (Nat.log 2 (hi - lo) + 1)`. With a test that charges one tick per probe (`c = 1`), this says
that bisection probes at most `⌊log₂ (hi - lo)⌋ + 1` times. -/
theorem lowerBoundM_time_le (t : ℕ → TimeM ℕ Bool) {c : ℕ} (hc : ∀ m, (t m).time ≤ c)
    (lo hi : ℕ) : (lowerBoundM t lo hi).time ≤ c * (Nat.log 2 (hi - lo) + 1) := by
  suffices h : (lowerBoundM t lo hi).time ≤ c * Nat.log 2 (2 * (hi - lo)) by
    rcases Nat.eq_zero_or_pos (hi - lo) with h0 | hpos
    · rw [h0] at h ⊢
      simp only [Nat.mul_zero, Nat.log_zero_right, Nat.zero_add, Nat.mul_one] at h ⊢
      omega
    · rw [show 2 * (hi - lo) = (hi - lo) * 2 by omega, Nat.log_mul_base (by omega) (by omega)]
        at h
      exact h
  generalize hk : hi - lo = k
  induction k using Nat.strong_induction_on generalizing lo hi with
  | _ k ih =>
    rw [lowerBoundM]
    split_ifs with hlt
    · simp only [TimeM.time_bind]
      set mid := (lo + hi) / 2 with hmid
      have hlog : 1 ≤ Nat.log 2 (2 * k) := by
        rw [show 2 * k = k * 2 by omega, Nat.log_mul_base (by omega) (by omega)]
        omega
      have hstep : ∀ k', 2 * k' ≤ k → c * Nat.log 2 (2 * k') + c ≤ c * Nat.log 2 (2 * k) := by
        intro k' h2
        rcases Nat.eq_zero_or_pos k' with h0 | hpos
        · subst h0
          simp only [Nat.mul_zero, Nat.log_zero_right]
          have := Nat.mul_le_mul_left c hlog
          omega
        · have := Nat.mul_le_mul_left c (log_two_mul_add_one_le hpos h2)
          rw [Nat.mul_add, Nat.mul_one] at this
          exact this
      have htc := hc mid
      cases hb : (t mid).ret
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have := ih (mid - lo) (by omega) (lo := lo) (hi := mid) rfl
        have := hstep (mid - lo) (by omega)
        omega
      · simp only [↓reduceIte]
        have := ih (hi - (mid + 1)) (by omega) (lo := mid + 1) (hi := hi) rfl
        have := hstep (hi - (mid + 1)) (by omega)
        omega
    · simp only [TimeM.time_pure, Nat.zero_le]

end Cslib.Algorithms.Lean
