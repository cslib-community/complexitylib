/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: candidate
import CslibFrontier.Computability.Complexity.Classes.Advice.LengthComparison

/-! # Exact-length advice comparison contracts

The displayed unbounded-gap hypothesis alone does not imply containment. In contrast, a
constant extra bit is safe even for an arbitrary, possibly noncomputable lower length.
-/

open Cslib.Complexity

-- Theorem 4.1's displayed capacity and unboundedness conditions alone do not imply inclusion.
example : ¬ ∀ lower gap : ℕ → ℕ,
    (∀ n, lower n + gap n ≤ 2 ^ n) → (∀ b, ∃ n, b < gap n) →
      PWithAdvice lower ⊆ PWithAdvice (fun n => lower n + gap n) := by
  intro h
  obtain ⟨lower, gap, L, _, _, _, hcap, hunbounded, hL, hnot⟩ :=
    exists_nonmonotone_advice_bounds
  exact hnot (h lower gap hcap hunbounded hL)

-- Baseline P/0 remains contained in every exact advice class.
example (length : ℕ → ℕ) : PWithAdvice (fun _ => 0) ⊆ PWithAdvice length := by
  rw [PWithAdvice_zero_eq_P]
  exact P_subset_PWithAdvice length

-- Repeated fixed-bit padding, without any length-computability assumption.
example (length : ℕ → ℕ) :
    PWithAdvice length ⊆ PWithAdvice (fun n => (length n + 1) + 1) :=
  (PWithAdvice_subset_succ length).trans (PWithAdvice_subset_succ (fun n => length n + 1))

-- A growing positive gap works even when the lower bound is arbitrary/noncomputable.
example (lower : ℕ → ℕ) :
    PWithAdvice lower ⊆ PWithAdvice (fun n => lower n + n + 1) :=
  PWithAdvice_subset_of_lt (fun _ => by omega)

-- Positivity is pointwise: no unboundedness or computability of the extra space is needed.
example (lower gap : ℕ → ℕ) (hgap : ∀ n, 0 < gap n) :
    PWithAdvice lower ⊆ PWithAdvice (fun n => lower n + gap n) :=
  PWithAdvice_subset_of_lt (fun n => by have := hgap n; omega)
