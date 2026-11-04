/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Nat.ResidueSum

/-! Exact counts from streamed residues: recovery below the modulus, and its failure above. -/

namespace ComplexityTests.ResidueSum

open Nat

-- The terms `8, 9, 10` are `0, 1, 2` modulo `8`, which sum to `3 < 8`: the streamed residue is
-- the count `3`, by the lemma and by evaluation.
example : (List.range 3).foldl (fun acc i => (acc + (8 + i)) % 8) 0 = 3 :=
  foldl_range_add_mod_eq_of_lt (g := fun i => i) (fun i _ => by omega) (by decide) (by decide)

example : (List.range 3).foldl (fun acc i => (acc + (8 + i)) % 8) 0 = 3 := by decide

-- Above the modulus the residue loses the count: two terms `5` sum to `10`, streamed as `2`.
example : (List.range 2).foldl (fun acc _ => (acc + 5) % 8) 0 = 2 ∧
    ∑ _i ∈ Finset.range 2, 5 = 10 := by decide

-- Streaming from a nonzero start adds its residue.
example (f : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldl (fun acc i => (acc + f i) % 2 ^ 5) (37 % 2 ^ 5) =
      (37 + ∑ i ∈ Finset.range n, f i) % 2 ^ 5 :=
  foldl_range_add_mod f _ 37 n

end ComplexityTests.ResidueSum
