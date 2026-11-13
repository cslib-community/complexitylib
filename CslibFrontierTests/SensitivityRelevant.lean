/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.QueryComplexity.RelevantCoordinates
import CslibFrontier.Foundations.Data.BitString.Parity

/-! # Sensitivity, relevance and local-boundary cardinality clients -/

set_option linter.privateModule false

namespace CslibFrontierTests.SensitivityRelevant

open Cslib Cslib.BitString Finset Function

-- A singleton spends every direction on its boundary, and attains equality.
example (n : ℕ) (x : Fin n → Bool) :
    #{i : Fin n | update x i (!x i) ∉ ({x} : Finset (Fin n → Bool))} = n := by
  simp

example (n : ℕ) (x : Fin n → Bool) :
    2 ^ n ≤ 2 ^ n * ({x} : Finset (Fin n → Bool)).card := by
  apply two_pow_le_two_pow_mul_card_of_boundary_bound _ n (by simp)
  intro y _
  simpa only [card_univ, Fintype.card_fin] using
    card_filter_le (univ : Finset (Fin n))
      (fun i => update y i (!y i) ∉ ({x} : Finset (Fin n → Bool)))

-- A nontrivial codimension-two subcube has two points, boundary budget two, and equality 8=4*2.
example :
    let A : Finset (Fin 3 → Bool) := {x | x 0 = false ∧ x 1 = true}
    A.card = 2 ∧ A.Nonempty ∧ ∀ x ∈ A, #{i | update x i (!x i) ∉ A} = 2 := by
  decide

example :
    let A : Finset (Fin 3 → Bool) := {x | x 0 = false ∧ x 1 = true}
    2 ^ 3 ≤ 2 ^ 2 * A.card := by
  apply two_pow_le_two_pow_mul_card_of_boundary_bound _ 2 (by decide)
  decide

-- Empty coordinates satisfy the all-relevant premise without acquiring a positive lower bound.
example (f : BooleanFunction 0) : Nat.clog 2 0 ≤ 3 * sensitivity f :=
  clog_le_three_mul_sensitivity_of_depends_on_all f fun i => Fin.elim0 i

example (n : ℕ) (b : Bool) :
    #{i : Fin n | ∃ x, IsSensitiveCoord (fun _ => b) x i} = 0 := by
  simp [IsSensitiveCoord]

-- One relevant coordinate, with two ignored coordinates, is counted as one rather than three.
private def projection : BooleanFunction 3 := fun x => x 0

private theorem projection_relevance : #{i : Fin 3 | ∃ x, IsSensitiveCoord projection x i} = 1 := by
  decide

example : sensitivity projection = 1 := by decide

example : 1 ≤ sensitivity projection * 4 ^ sensitivity projection := by
  simpa only [projection_relevance] using card_relevant_le_sensitivity_mul_four_pow projection

example : #{i : Fin 1 | ∃ x, IsSensitiveCoord (fun y => y 0) x i} = 1 := by decide

-- All coordinates of parity are relevant, so the logarithmic corollary applies for every n.
example (n : ℕ) : Nat.clog 2 n ≤ 3 * sensitivity (parity n) := by
  apply clog_le_three_mul_sensitivity_of_depends_on_all
  intro i
  refine ⟨fun _ => false, ?_⟩
  rw [IsSensitiveCoord, parity_update_not]
  exact Bool.not_ne_self _

end CslibFrontierTests.SensitivityRelevant
