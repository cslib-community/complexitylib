/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitialVector
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitialChunkCorrect

/-!
# Correct paid initial-source vectors

Sufficient actual capacity yields every requested initial coordinate. These are the existing
packed source values, including partial final chunks; no alternate leaf semantics is used.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.InitialVector

open Cslib.TreeEval.Ary

variable {k s : ℕ} {Q : Type}

/-- Sufficient binary capacity recovers the full requested initial vector. -/
theorem values_of_capacity (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (limit m r : ℕ) (hcapacity : r ≤ limit.size) :
    values M e (limit, m, r) =
      List.ofFn (fun j : Fin r => InitialChunk.chunk M e (m, j)) := by
  rw [values_eq_ofFn, Nat.min_eq_left hcapacity]

/-- The full paid leaf vector is exactly the existing packed initial view. -/
theorem values_eq_packBits {r m : ℕ} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (limit b : ℕ) [NeZero b] (hcapacity : r ≤ limit.size)
    (hb : Encoding.width k s b ≤ r * m) :
    values M e (limit, m, r) = List.ofFn (fun j : Fin r =>
      (Packed.packBits hb
        (Encoding.encode e (some (initialView (MultiTapePTM.ofDeterministic M) b))) j).val) := by
  rw [values_of_capacity M e limit m r hcapacity]
  congr 1
  funext j
  exact InitialChunk.chunk_eq_packBits M e b hb j

end Turing.MultiTapePTM.BlockComputation.InitialVector
