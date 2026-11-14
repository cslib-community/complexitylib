/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.SeededRankQuery

open Cslib Cslib.BitString Cslib.PacketPacking Cslib.BalancedSchedules
open Cslib.Circuits.Boolean.CarrySaveQuery
open Cslib.Circuits.Frontier.SeededRankQuery

private abbrev vertex : Fin 1 ⊕ Fin 1 ↪ Fin 2 := finSumFinEquiv.toEmbedding

-- Four parallel edges have ranks0,1,2,3 for every seed. Two bits suffice for the last rank,
-- although they would not suffice to count four true predicates.
example (seed : SeededLabels.Seed 2 6) :
    (equivFin 2 (Counting.count 4 2
      (predicate 2 1 vertex (fun _ : Fin 4 => 0) (fun _ : Fin 4 => 0) seed 3)) : ℕ) = 3 := by
  change (equivFin (Nat.clog 2 4) (Counting.count 4 (Nat.clog 2 4) _) : ℕ) = _
  rw [val_count_rank]
  simp only [Seeded.rank, classIndex, pairLabel, and_true]
  decide

-- The zero-bit singleton case is also an actual counting-tree client.
example (seed : SeededLabels.Seed 2 6) :
    (equivFin 0 (Counting.count 1 0
      (predicate 2 1 vertex (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) seed 0)) : ℕ) = 0 := by
  simp

-- Out-of-range leaf addresses do not invoke a predecessor test.
example (seed : SeededLabels.Seed 2 6) :
    predicate 2 1 vertex (fun _ : Fin 4 => 0) (fun _ : Fin 4 => 0) seed 3 5 = false := by
  simp [predicate]
