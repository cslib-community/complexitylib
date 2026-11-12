/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Foundations.Combinatorics.SeededPackingRank
import Mathlib.Tactic.FinCases

open Cslib.PacketPacking Cslib.PacketPacking.Seeded Cslib.BalancedSchedules Finset

private abbrev vertex : Fin 1 ⊕ Fin 1 ↪ Fin 2 := finSumFinEquiv.toEmbedding
private abbrev endpoint (_ : Fin 4) : Fin 1 := 0

/- Four parallel edges all have the same class for every seed, even with a nonempty label word.
Their ranks depend on edge order, not on the outcome of hashing. -/
private theorem parallel_rank (seed : SeededLabels.Seed 2 6) (e : Fin 4) :
    rank 2 1 vertex endpoint endpoint seed e = e.val := by
  fin_cases e <;>
    simp only [rank, classIndex, pairLabel, endpoint, and_true] <;> decide

example (seed : SeededLabels.Seed 2 6) :
    (∑ candidate, (predecessor 2 1 vertex endpoint endpoint seed 3 candidate).toNat) = 3 := by
  rw [← rank_eq_sum_predecessors, parallel_rank]
  rfl

/- Both bits of the true final rank are accepted. -/
example (seed : SeededLabels.Seed 2 6) :
    ∀ j : Fin 2, (3 : ℕ).testBit j.val =
      (∑ candidate,
        (predecessor 2 1 vertex endpoint endpoint seed 3 candidate).toNat).testBit j.val :=
  (eq_rank_iff_predecessor_bits 2 1 vertex endpoint endpoint seed 3
    (width := 2) (by decide) (by decide)).mp (parallel_rank seed 3).symm

/- A forged low bit is rejected by the verification contract. -/
example (seed : SeededLabels.Seed 2 6) :
    ¬ ∀ j : Fin 2, (2 : ℕ).testBit j.val =
      (∑ candidate,
        (predecessor 2 1 vertex endpoint endpoint seed 3 candidate).toNat).testBit j.val := by
  rw [← eq_rank_iff_predecessor_bits 2 1 vertex endpoint endpoint seed 3
    (width := 2) (by decide) (by decide), parallel_rank]
  decide

/- Dropping the guess-width bound is unsound: seven and the true rank three have identical
low two bits. The contract excludes seven because it is not a two-bit guess. -/
example (seed : SeededLabels.Seed 2 6) :
    (∀ j : Fin 2, (7 : ℕ).testBit j.val =
      (∑ candidate,
        (predecessor 2 1 vertex endpoint endpoint seed 3 candidate).toNat).testBit j.val) ∧
      7 ≠ rank 2 1 vertex endpoint endpoint seed 3 ∧ ¬ (7 < 2 ^ 2) := by
  rw [← rank_eq_sum_predecessors, parallel_rank]
  decide

/- A singleton graph needs zero rank bits, and the bounded guess is necessarily zero. -/
example (seed : SeededLabels.Seed 2 6) :
    rank 2 1 vertex (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) seed 0 = 0 := by
  symm
  apply (eq_rank_iff_predecessor_bits 2 1 vertex
    (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) seed 0
    (width := 0) (by decide) (by decide)).mpr
  intro j
  exact Fin.elim0 j
