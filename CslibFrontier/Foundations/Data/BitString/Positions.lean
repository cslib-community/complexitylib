/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString

/-!
# The positions of the ones of a bit string

`Cslib.BitString.positions x` lists the coordinates where `x : BitString n` is `true`, in increasing
order and without repetition. Streaming reductions from set disjointness read a bit string as the
stream of its positions.

## Main definitions

* `Cslib.BitString.positions`: the coordinates of the ones of a bit string, as a list.

## Main results

* `Cslib.BitString.mem_positions`, `Cslib.BitString.nodup_positions`,
  `Cslib.BitString.length_positions_le`: membership, no repetition, and length at most `n`.
-/

public section

namespace Cslib.BitString

/-- The coordinates where a bit string is `true`, in increasing order. -/
def positions {n : ℕ} (x : BitString n) : List (Fin n) :=
  (List.finRange n).filter fun i => x i

@[simp] theorem mem_positions {n : ℕ} {x : BitString n} {i : Fin n} :
    i ∈ positions x ↔ x i = true := by
  simp [positions, List.mem_finRange]

theorem nodup_positions {n : ℕ} (x : BitString n) : (positions x).Nodup :=
  (List.nodup_finRange n).filter _

theorem length_positions_le {n : ℕ} (x : BitString n) : (positions x).length ≤ n := by
  have h := List.length_filter_le (fun i : Fin n => x i) (List.finRange n)
  rwa [List.length_finRange] at h

end Cslib.BitString
