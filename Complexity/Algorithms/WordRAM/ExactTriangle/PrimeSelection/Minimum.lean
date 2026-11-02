/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.NumberTheory.SqrtPrimeWindow

/-!
# Internal minimum invariant for the native selector

The invariant describes the actual result/flag words before candidate `k`. It distinguishes
an empty eligible prefix from a genuine attained minimum; a zero score is never mistaken for
an uninitialized result. The selector's loop proof imports these private proof helpers with
`import all`. They introduce no alternative prime-selection problem or counting algorithm.
-/

-- This proof-only companion is intentionally private; the native step proof imports all.
set_option linter.privateModule false

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

private def BestBefore (D : ℕ) (score : ℕ → ℕ) (k best value found : ℕ) : Prop :=
  (found = 0 ∧ best = 0 ∧ ∀ p ∈ Nat.sqrtPrimeWindow D, p < k → False) ∨
    (found = 1 ∧ best ∈ Nat.sqrtPrimeWindow D ∧ best < k ∧ value = score best ∧
      ∀ p ∈ Nat.sqrtPrimeWindow D, p < k → value ≤ score p)

private theorem bestBefore_initial (D : ℕ) (score : ℕ → ℕ) :
    BestBefore D score 2 0 0 0 := by
  refine Or.inl ⟨rfl, rfl, ?_⟩
  intro p hp hlt
  have := (Nat.mem_sqrtPrimeWindow_iff_sq.1 hp).1.two_le
  omega

private theorem bestBefore_skip {D k best value found : ℕ} {score : ℕ → ℕ}
    (h : BestBefore D score k best value found) (hk : k ∉ Nat.sqrtPrimeWindow D) :
    BestBefore D score (k + 1) best value found := by
  obtain ⟨hf, hb, hnone⟩ | ⟨hf, hb, hlt, hv, hmin⟩ := h
  · refine Or.inl ⟨hf, hb, ?_⟩
    intro p hp hpk
    have hne : p ≠ k := by intro he; subst p; exact hk hp
    exact hnone p hp (by omega)
  · refine Or.inr ⟨hf, hb, by omega, hv, ?_⟩
    intro p hp hpk
    have hne : p ≠ k := by intro he; subst p; exact hk hp
    exact hmin p hp (by omega)

private theorem bestBefore_take {D k best value found : ℕ} {score : ℕ → ℕ}
    (h : BestBefore D score k best value found) (hk : k ∈ Nat.sqrtPrimeWindow D) :
    BestBefore D score (k + 1)
      (if found = 0 ∨ score k < value then k else best)
      (if found = 0 ∨ score k < value then score k else value) 1 := by
  obtain ⟨hf, _, hnone⟩ | ⟨hf, hb, hlt, hv, hmin⟩ := h
  · simp only [hf, true_or, ↓reduceIte]
    refine Or.inr ⟨rfl, hk, by omega, rfl, ?_⟩
    intro p hp hpk
    by_cases he : p = k
    · subst p
      exact le_rfl
    · exact False.elim (hnone p hp (by omega))
  · simp only [hf, one_ne_zero, false_or]
    by_cases himprove : score k < value
    · simp only [himprove, ↓reduceIte]
      refine Or.inr ⟨rfl, hk, by omega, rfl, ?_⟩
      intro p hp hpk
      by_cases he : p = k
      · subst p
        exact le_rfl
      · exact himprove.le.trans (hmin p hp (by omega))
    · simp only [himprove, ↓reduceIte]
      refine Or.inr ⟨rfl, hb, by omega, hv, ?_⟩
      intro p hp hpk
      by_cases he : p = k
      · subst p
        exact Nat.le_of_not_gt himprove
      · exact hmin p hp (by omega)

private theorem window_lt_of_exit {D k p : ℕ} (hp : p ∈ Nat.sqrtPrimeWindow D)
    (hstop : D ≤ k * k) : p < k := by
  have hs : p * p < D := by
    simpa only [pow_two] using (Nat.mem_sqrtPrimeWindow_iff_sq.1 hp).2.2
  by_contra h
  have hm : k * k ≤ p * p := Nat.mul_self_le_mul_self (Nat.le_of_not_gt h)
  omega

private theorem bestBefore_exit {D k best value found : ℕ} {score : ℕ → ℕ}
    (h : BestBefore D score k best value found) (hne : (Nat.sqrtPrimeWindow D).Nonempty)
    (hstop : D ≤ k * k) :
    found = 1 ∧ best ∈ Nat.sqrtPrimeWindow D ∧ value = score best ∧
      ∀ p ∈ Nat.sqrtPrimeWindow D, value ≤ score p := by
  obtain ⟨_, _, hnone⟩ | ⟨hf, hb, _, hv, hmin⟩ := h
  · obtain ⟨p, hp⟩ := hne
    exact False.elim (hnone p hp (window_lt_of_exit hp hstop))
  · exact ⟨hf, hb, hv, fun p hp => hmin p hp (window_lt_of_exit hp hstop)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
