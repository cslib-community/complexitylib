/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.CountingQuery
public import CslibFrontier.Foundations.Combinatorics.SeededPackingRank

/-!
# Seeded packet ranks as streamed Boolean counts

For edges numbered by `Fin n`, the predecessor predicate supplies one bit per leaf of the
streamed counting tree. Its final value is exactly the seeded class rank at precision
`clog 2 n`, including power-of-two edge counts. No invocation of a general counting-machine
simulation is used. This is an arithmetic correctness bridge, not a native cost theorem:
endpoint decoding, hashing, and the complete alternating evaluator remain to be implemented.
-/

public section

namespace Cslib.Circuits.Frontier.SeededRankQuery

open Cslib.PacketPacking Cslib.BalancedSchedules Cslib.BitString
open Cslib.Circuits.Boolean.CarrySaveQuery

variable {n : ℕ} {R C : Type*}
  (U a : ℕ) (vertex : R ⊕ C ↪ Fin U) (rowOf : Fin n → R) (colOf : Fin n → C)
  (seed : SeededLabels.Seed U (6 * a)) (e : Fin n)

/-- One fixed seed's predecessor test, with false padding beyond the edge universe. -/
@[expose] noncomputable def predicate (j : ℕ) : Bool :=
  if h : j < n then Seeded.predecessor U a vertex rowOf colOf seed e ⟨j, h⟩ else false

/-- The predicate's finite sum is the original packing's class rank. -/
theorem sum_predicate :
    (∑ j ∈ Finset.range n, (predicate U a vertex rowOf colOf seed e j).toNat) =
      Seeded.rank U a vertex rowOf colOf seed e := by
  rw [Seeded.rank_eq_sum_predecessors, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [predicate, j.isLt]

/-- The streamed counting circuit returns the exact rank using only `clog 2 n` output bits. -/
theorem val_count_rank :
    (equivFin (Nat.clog 2 n)
      (Counting.count n (Nat.clog 2 n) (predicate U a vertex rowOf colOf seed e)) : ℕ) =
      Seeded.rank U a vertex rowOf colOf seed e := by
  rw [Counting.val_count, sum_predicate, Nat.mod_eq_of_lt]
  exact (Seeded.rank_lt_card U a vertex rowOf colOf seed e).trans_le
    (by simpa using Nat.le_pow_clog (by decide : 1 < 2) n)

end Cslib.Circuits.Frontier.SeededRankQuery
