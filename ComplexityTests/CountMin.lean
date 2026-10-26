/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Algorithms.Streaming.CountMin.LinearHash
public import Complexity.Algorithms.Streaming.CountMin.Program
import Mathlib.Tactic.NormNum

/-! # Count-Min clients

The executable examples check stored rows, weighted updates, an absent queried item, and merging.
The probabilistic example instantiates the proved bound with an existing concrete universal hash
family, four buckets and three independent rows.
-/

public section

namespace ComplexityTests.CountMin

open Cslib Cslib.CountMin Cslib.Probability

/-- Two rows distinguishing the low and high bits of a two-bit item. -/
private def hashBank (r : Fin 2) (x : Fin 4) : Fin 2 :=
  if r = 0 then ⟨x.val % 2, Nat.mod_lt _ (by decide)⟩
  else ⟨x.val / 2, by omega⟩

/-- Three distinct items with unequal positive weights; item `3` never occurs. -/
private def stream : List (Fin 4 × ℕ) := [(0, 2), (1, 3), (2, 5)]

-- This checks the actual nested-vector representation, including collisions in both rows.
example : ((run hashBank stream).toList.map Vector.toList) = [[7, 3], [5, 5]] := by
  decide

example : List.ofFn (fun x : Fin 4 => estimate hashBank (run hashBank stream) x) =
    [5, 3, 5, 3] := by
  decide

-- An absent item can have a positive estimate; Count-Min's guarantee is one-sided.
example : frequency stream 3 = 0 ∧ estimate hashBank (run hashBank stream) 3 = 3 := by
  decide

example (x : Fin 4) : frequency stream x ≤ estimate hashBank (run hashBank stream) x :=
  frequency_le_estimate_run hashBank stream x

-- A repeated item adds its entire weight to the two addressed counters.
example : ((update hashBank (run hashBank stream) (0, 4)).toList.map Vector.toList) =
    [[11, 3], [9, 5]] := by
  decide

example : merge (run hashBank [(0, 2)]) (run hashBank [(1, 3), (2, 5)]) =
    run hashBank stream := by
  decide

example : ((run hashBank []).toList.map Vector.toList) = [[0, 0], [0, 0]] ∧
    estimate hashBank (run hashBank []) 3 = 0 := by
  decide

-- Zero mass does not require the stream to be empty.
example : mass ([(0, 0), (2, 0)] : List (Fin 4 × ℕ)) = 0 ∧
    run hashBank [(0, 0), (2, 0)] = zero 2 2 ∧
    ∀ x : Fin 4, estimate hashBank (run hashBank [(0, 0), (2, 0)]) x = 0 := by
  decide

/-- Four buckets and three independent matrix seeds give additive error at most half the mass,
except on at most one eighth of the hash banks, for any fixed stream and query. -/
theorem fixed_query_error_le_one_eighth {n : ℕ} (s : List (BitString n × ℕ)) (x : BitString n) :
    (Finset.dens {seeds : Fin 3 → Fin 2 → BitString n |
      (frequency s x : ℝ) + (1 / 2 : ℝ) * mass s <
        (estimate (fun r => indexedHash (seeds r))
          (run (fun r => indexedHash (seeds r)) s) x : ℝ)} : ℝ) ≤ 1 / 8 := by
  convert dens_estimate_error_le_inv_two_pow (d := 3)
    (indexedHash (n := n) (m := 2)) (isTwoUniversal_indexedHash n 2) s x
    (ε := (1 / 2 : ℝ)) (by norm_num) (by norm_num) using 1
  norm_num

-- The same theorem accepts a nonempty stream of total weight zero.
example {n : ℕ} (item x : BitString n) :
    (Finset.dens {seeds : Fin 3 → Fin 2 → BitString n |
      0 < (estimate (fun r => indexedHash (seeds r))
        (run (fun r => indexedHash (seeds r)) [(item, 0)]) x : ℝ)} : ℝ) ≤ 1 / 8 := by
  have h := dens_estimate_error_le_inv_two_pow (d := 3)
    (indexedHash (n := n) (m := 2)) (isTwoUniversal_indexedHash n 2) [(item, 0)] x
    (ε := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  norm_num [frequency, mass] at h ⊢
  exact h

-- A concrete sampler satisfies the uniformity premise of the probabilistic-program theorem.
example {n : ℕ} (s : List (BitString n × ℕ)) (x : BitString n) :
    ((ProbComp.eval (sampleQuery (d := 3) (ProbComp.uniform (Fin 2 → BitString n))
      (indexedHash (n := n) (m := 2)) s x)).toOuterMeasure
        {answer | (frequency s x : ℝ) + (1 / 2 : ℝ) * mass s < (answer : ℝ)}).toReal ≤
      1 / 8 := by
  convert sampleQuery_error_le_inv_two_pow (d := 3)
    (ProbComp.uniform (Fin 2 → BitString n)) (ProbComp.eval_uniform (Fin 2 → BitString n))
    (indexedHash (n := n) (m := 2)) (isTwoUniversal_indexedHash n 2) s x
    (ε := (1 / 2 : ℝ)) (by norm_num) (by norm_num) using 1
  norm_num

end ComplexityTests.CountMin
