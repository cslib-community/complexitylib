/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of CslibFrontier.Computability.Kolmogorov.TimeBounded.Counting)

import CslibFrontier.Computability.Kolmogorov.TimeBounded.Counting

/-! # Tests for counting objects of small `K^t` -/

namespace CslibFrontierTests.KolmogorovTimeBoundedCounting

open Cslib Cslib.Kolmogorov

/-- At most 127 of the 256 Boolean functions on three inputs have truth tables of `K^t` at
most 6, whatever the step budget. -/
example (t : ℕ) :
    (Finset.univ.filter fun h : BooleanFunction 3 =>
      timeBoundedAt t (List.ofFn fun i => h ((BitString.equivFin 3).symm i)) ≤ 6).card ≤ 127 :=
  Nat.le_of_lt_succ (card_filter_timeBoundedAt_truthTable_le_lt 3 t 6)

/-- Hence, for every step budget, some Boolean function on three inputs has a truth table of `K^t`
greater than 6. -/
example (t : ℕ) : ∃ h : BooleanFunction 3,
    ((6 : ℕ) : ℕ∞) < timeBoundedAt t (List.ofFn fun i => h ((BitString.equivFin 3).symm i)) := by
  by_contra! hall
  have hlt := card_filter_timeBoundedAt_truthTable_le_lt 3 t 6
  rw [Finset.filter_true_of_mem fun h _ => hall h, Finset.card_univ] at hlt
  simp [Fintype.card_bool, Fintype.card_fin] at hlt

/-- The generic bound applies to any injective encoding, here unary notation. -/
example (t s : ℕ) : {n : ℕ | timeBoundedAt t (List.replicate n true) ≤ s}.encard < 2 ^ (s + 1) :=
  encard_setOf_timeBoundedAt_le_lt (List.replicate_left_injective true) t s

end CslibFrontierTests.KolmogorovTimeBoundedCounting
