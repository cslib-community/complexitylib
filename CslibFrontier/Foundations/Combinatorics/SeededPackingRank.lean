/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SeededPacking
public import CslibFrontier.Foundations.Data.BitString.List.LowBits
public import Mathlib.Data.Nat.Log

/-!
# Verifying the rank of an edge in a seeded packing

The existing packet placement numbers an edge by the number of earlier edges in its class.
For a fixed seed, this rank is a sum of Boolean tests, each reading just the two endpoints of
the queried edge and one candidate predecessor. A bounded proposed rank equals this count
exactly when all bits below the chosen width agree. The bound on the proposal is necessary:
checking low bits alone would accept a larger number with the same residue.

These are exact mathematical verification contracts. They neither implement an alternating
counting machine nor bound the cost of endpoint access, hashing, or counting.
-/

public section

namespace Cslib.PacketPacking.Seeded

open Cslib.BalancedSchedules Cslib.BitString Finset

variable {E R C : Type*} [Fintype E] [LinearOrder E]

/-- The original `classIndex`, with both endpoint labels decoded from the fixed seed. -/
noncomputable abbrev rank (U a : ℕ) (vertex : R ⊕ C ↪ Fin U) (rowOf : E → R) (colOf : E → C)
    (seed : SeededLabels.Seed U (6 * a)) (e : E) : ℕ :=
  classIndex rowOf colOf
    (fun r => label U a seed (vertex (.inl r)))
    (fun c => label U a seed (vertex (.inr c))) e

/-- One predecessor test compares the two endpoint words; no full packing is constructed. -/
@[expose] noncomputable def predecessor (U a : ℕ) (vertex : R ⊕ C ↪ Fin U)
    (rowOf : E → R) (colOf : E → C) (seed : SeededLabels.Seed U (6 * a))
    (e candidate : E) : Bool :=
  decide (candidate < e ∧
    label U a seed (vertex (.inl (rowOf candidate))) = label U a seed (vertex (.inl (rowOf e))) ∧
    label U a seed (vertex (.inr (colOf candidate))) = label U a seed (vertex (.inr (colOf e))))

variable (U a : ℕ) (vertex : R ⊕ C ↪ Fin U) (rowOf : E → R) (colOf : E → C)
  (seed : SeededLabels.Seed U (6 * a)) (e : E)

/-- The original class rank is exactly the sum of the individual predecessor bits. -/
theorem rank_eq_sum_predecessors :
    rank U a vertex rowOf colOf seed e =
      ∑ candidate, (predecessor U a vertex rowOf colOf seed e candidate).toNat := by
  simp only [rank, classIndex, pairLabel, Prod.mk.injEq, predecessor]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro candidate _
  split_ifs with h
  · rw [decide_eq_true h]
    rfl
  · rw [decide_eq_false h]
    rfl

/-- Even the last edge has rank strictly less than the number of edges. -/
theorem rank_lt_card : rank U a vertex rowOf colOf seed e < Fintype.card E := by
  have h := classIndex_lt_occupancy rowOf colOf
    (fun r => label U a seed (vertex (.inl r)))
    (fun c => label U a seed (vertex (.inr c))) e
  refine h.trans_le ?_
  rw [occupancy, Fintype.card_subtype]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- With enough bits for every edge rank, the true rank is the unique bounded guess whose
bits agree with the predecessor count. In particular, all queried bits share one fixed seed. -/
theorem eq_rank_iff_predecessor_bits {width guess : ℕ}
    (hwidth : Fintype.card E ≤ 2 ^ width) (hguess : guess < 2 ^ width) :
    guess = rank U a vertex rowOf colOf seed e ↔
      ∀ j : Fin width, guess.testBit j.val =
        (∑ candidate,
          (predecessor U a vertex rowOf colOf seed e candidate).toNat).testBit j.val := by
  rw [← rank_eq_sum_predecessors]
  constructor
  · rintro rfl j
    rfl
  · intro h
    apply lowBits_injective_of_lt hguess
      ((rank_lt_card U a vertex rowOf colOf seed e).trans_le hwidth)
    rw [lowBits_eq_ofFn, lowBits_eq_ofFn]
    exact congrArg List.ofFn (funext h)

/-- The ceiling binary logarithm of the edge count is sufficient, including the singleton
case where the only possible rank is zero and no rank bits need checking. -/
theorem eq_rank_iff_clog_predecessor_bits {guess : ℕ}
    (hguess : guess < 2 ^ Nat.clog 2 (Fintype.card E)) :
    guess = rank U a vertex rowOf colOf seed e ↔
      ∀ j : Fin (Nat.clog 2 (Fintype.card E)), guess.testBit j.val =
        (∑ candidate,
          (predecessor U a vertex rowOf colOf seed e candidate).toNat).testBit j.val :=
  eq_rank_iff_predecessor_bits U a vertex rowOf colOf seed e
    (Nat.le_pow_clog (by decide) _) hguess

end Cslib.PacketPacking.Seeded
