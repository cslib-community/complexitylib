/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Expectation
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Parameters
public import Mathlib.Basic.Real.Basic

/-!
# Clocked copies and independent repetition

The worst-case form of [ChanItakuraMaYu2026], Corollary 2.4: `R` independent copies of the
reduction, each run under a step counter.

* `copyM m T A B C q ss` runs `threeSumM` with the parameters of unit `m`, the prime `q` and the
  seeds `ss`, under a step counter of `T` ticks: if the run would take more than `T` ticks it is cut
  off, charged `T` ticks, and reports nothing. The counter itself is not charged.
* `corollaryM m T R A B C qs ωs` runs `R` copies with primes `qs i` and seeds `ωs i` and reports
  the union. It costs at most `R (T + |C|) + |C|` ticks for **every** choice of the random
  numbers (`time_corollaryM_le`), and every reported value is a sum
  (`exists_add_eq_of_mem_ret_corollaryM`).

**The random experiment.** The primes `qs i` are independent and uniform on the window
`[2 ^ d, 2 ^ (d + 1))`; given them, the seeds `ωs i` are independent and uniform on
`seeds (qs i) ^ μ`. `allFailProb` is the probability that no copy reports `c`, computed as the
average over the primes of the fraction of seed choices, and it is the `R`-th power of the
probability `copyFailProb` that one copy misses `c` (`allFailProb_eq_pow`).

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Params Cslib.Algorithms.Lean.TimeM

/-- The seeds for the modulus `q` (empty for `q = 0`). -/
@[expose] def seedsOf (q : ℕ) : Finset (Seed q) :=
  if h : q ≠ 0 then haveI : NeZero q := ⟨h⟩; seeds q else ∅

theorem seedsOf_eq (q : ℕ) [Fact q.Prime] : seedsOf q = seeds q := by
  unfold seedsOf
  rw [dite_eq_left_of_eq_true (eq_true (Fact.out : q.Prime).ne_zero)]

/-- **One clocked copy**: the reduction with the parameters of unit `m`, run under a step counter of
`T` ticks; a run that would exceed `T` is cut off, charged `T`, and reports nothing. -/
@[expose] def copyM (m T : ℕ) (A B C : List ℕ) (q : ℕ) (ss : Fin (μ m) → Seed q) :
    TimeM ℕ (List ℕ) :=
  if (threeSumM (d m) (t m) (s m) q (List.ofFn ss) A B C).time ≤ T then
    threeSumM (d m) (t m) (s m) q (List.ofFn ss) A B C
  else ⟨[], T⟩

/-- **`R` clocked copies**, reporting the union of their reports. -/
@[expose] def corollaryM (m T R : ℕ) (A B C : List ℕ) (qs : Fin R → ℕ)
    (ωs : (i : Fin R) → Fin (μ m) → Seed (qs i)) : TimeM ℕ (List ℕ) := do
  let outs ← (List.finRange R).mapM fun i => copyM m T A B C (qs i) (ωs i)
  let yes := outs.flatten
  ✓[yes.length] filterTickM (· ∈ yes) C

theorem time_copyM_le (m T : ℕ) (A B C : List ℕ) (q : ℕ) (ss : Fin (μ m) → Seed q) :
    (copyM m T A B C q ss).time ≤ T := by
  unfold copyM; split_ifs with h <;> simp [h]

theorem ret_copyM_subset (m T : ℕ) (A B C : List ℕ) (q : ℕ) (ss : Fin (μ m) → Seed q) :
    ∀ c ∈ (copyM m T A B C q ss).ret, c ∈ C ∧
      ∃ a ∈ A, ∃ b ∈ B, a + b = c := by
  intro c hc
  unfold copyM at hc
  split_ifs at hc with h
  · refine ⟨?_, exists_add_eq_of_mem_ret_threeSumM (by unfold s t; omega) hc⟩
    rw [ret_threeSumM _ A B C (by unfold s t; omega)] at hc
    exact List.mem_of_mem_filter hc
  · simp at hc

theorem length_ret_copyM_le (m T : ℕ) (A B C : List ℕ) (q : ℕ) (ss : Fin (μ m) → Seed q) :
    (copyM m T A B C q ss).ret.length ≤ C.length := by
  unfold copyM
  split_ifs with h
  · rw [ret_threeSumM _ A B C (by unfold s t; omega)]
    exact List.length_filter_le _ _
  · simp

theorem ret_corollaryM (m T R : ℕ) (A B C : List ℕ) (qs : Fin R → ℕ)
    (ωs : (i : Fin R) → Fin (μ m) → Seed (qs i)) :
    (corollaryM m T R A B C qs ωs).ret =
      C.filter fun c => decide (∃ i, c ∈ (copyM m T A B C (qs i) (ωs i)).ret) := by
  simp only [corollaryM, ret_bind, ret_listMapM, ret_filterTickM]
  refine List.filter_congr fun c _ => ?_
  simp [List.mem_flatten, List.mem_map]

/-- **Soundness**: every reported value is a sum `a + b` with `a ∈ A`, `b ∈ B`. -/
theorem exists_add_eq_of_mem_ret_corollaryM {m T R : ℕ} {A B C : List ℕ} {qs : Fin R → ℕ}
    {ωs : (i : Fin R) → Fin (μ m) → Seed (qs i)} {c : ℕ}
    (hc : c ∈ (corollaryM m T R A B C qs ωs).ret) : ∃ a ∈ A, ∃ b ∈ B, a + b = c := by
  rw [ret_corollaryM] at hc
  obtain ⟨i, hi⟩ := of_decide_eq_true (List.mem_filter.mp hc).2
  exact (ret_copyM_subset m T A B C (qs i) (ωs i) c hi).2

/-- **Worst-case cost**: `R` copies cost at most `R (T + |C|) + |C|` ticks, for every choice of the
random numbers. -/
theorem time_corollaryM_le (m T R : ℕ) (A B C : List ℕ) (qs : Fin R → ℕ)
    (ωs : (i : Fin R) → Fin (μ m) → Seed (qs i)) :
    (corollaryM m T R A B C qs ωs).time ≤ R * (T + C.length) + C.length := by
  simp only [corollaryM, time_bind, time_listMapM, ret_listMapM, time_tick,
    time_filterTickM, List.length_flatten, List.map_map]
  have h1 : ((List.finRange R).map fun i => (copyM m T A B C (qs i) (ωs i)).time).sum ≤ R * T := by
    have := List.sum_le_length_nsmul ((List.finRange R).map fun i =>
      (copyM m T A B C (qs i) (ωs i)).time) T (by
        intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact time_copyM_le _ _ _ _ _ _ _)
    simpa using this
  have h2 : ((List.finRange R).map
      ((List.length ∘ fun i => (copyM m T A B C (qs i) (ωs i)).ret))).sum
      ≤ R * C.length := by
    have := List.sum_le_length_nsmul ((List.finRange R).map (List.length ∘ fun i =>
      (copyM m T A B C (qs i) (ωs i)).ret)) C.length (by
        intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
        exact length_ret_copyM_le _ _ _ _ _ _ _)
    simpa using this
  nlinarith

/-! ### The probability that every copy misses -/

/-- The probability that one clocked copy with prime `q` misses `c`, over its `μ` uniform seeds. -/
@[expose] noncomputable def copyMissFrac (m T : ℕ) (A B C : List ℕ) (c q : ℕ) : ℝ :=
  (#((Fintype.piFinset fun _ : Fin (μ m) => seedsOf q).filter fun ss =>
    c ∉ (copyM m T A B C q ss).ret) : ℝ) / (#(seedsOf q) : ℝ) ^ μ m

/-- The probability that one clocked copy misses `c`: a uniform prime of the window, then `μ`
uniform seeds. -/
@[expose] noncomputable def copyFailProb (m T : ℕ) (A B C : List ℕ) (c : ℕ) : ℝ :=
  (∑ q ∈ primeWindow (d m), copyMissFrac m T A B C c q) / #(primeWindow (d m))

/-- The probability that all of `R` independent clocked copies miss `c`: independent uniform primes
`qs`, then, given them, independent uniform seeds `ωs`. -/
@[expose] noncomputable def allFailProb (m T R : ℕ) (A B C : List ℕ) (c : ℕ) : ℝ :=
  (∑ qs ∈ Fintype.piFinset (fun _ : Fin R => primeWindow (d m)),
    (#((Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin (μ m) => seedsOf (qs i)).filter
        fun ωs => c ∉ (corollaryM m T R A B C qs ωs).ret) : ℝ) /
      #(Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin (μ m) => seedsOf (qs i))) /
    (#(primeWindow (d m)) : ℝ) ^ R

/-- **Independent repetition**: for `c ∈ C`, all `R` copies miss `c` with probability
`copyFailProb ^ R`. -/
theorem allFailProb_eq_pow {m T R : ℕ} {A B C : List ℕ} {c : ℕ} (hc : c ∈ C) :
    allFailProb m T R A B C c = copyFailProb m T A B C c ^ R := by
  unfold allFailProb copyFailProb
  have hinner : ∀ qs : Fin R → ℕ,
      (#((Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin (μ m) => seedsOf (qs i)).filter
        fun ωs => c ∉ (corollaryM m T R A B C qs ωs).ret) : ℝ) /
      #(Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin (μ m) => seedsOf (qs i)) =
      ∏ i, copyMissFrac m T A B C c (qs i) := fun qs => by
    have hset : ((Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin (μ m) =>
        seedsOf (qs i)).filter fun ωs => c ∉ (corollaryM m T R A B C qs ωs).ret) =
        Fintype.piFinset fun i => (Fintype.piFinset fun _ : Fin (μ m) => seedsOf (qs i)).filter
          fun ss => c ∉ (copyM m T A B C (qs i) ss).ret := by
      ext ωs
      simp only [mem_filter, Fintype.mem_piFinset, ret_corollaryM, List.mem_filter, hc,
        decide_eq_true_eq, true_and, not_exists]
      constructor
      · rintro ⟨h1, h2⟩ i; exact ⟨h1 i, h2 i⟩
      · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
    rw [hset, Fintype.card_piFinset, Fintype.card_piFinset]
    push_cast
    rw [← prod_div_distrib]
    refine prod_congr rfl fun i _ => ?_
    unfold copyMissFrac
    rw [Fintype.card_piFinset_const]
    push_cast; rfl
  simp only [hinner]
  rw [← Finset.prod_univ_sum, Finset.prod_const, card_univ, Fintype.card_fin, div_pow]

end Cslib.Algorithms.Lean.SubsetConvThreeSum
