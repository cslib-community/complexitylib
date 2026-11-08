/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import Complexity.Foundations.GroupTheory.Perm.SelectedOrbits
import Complexity.Foundations.GroupTheory.Perm.InvariantPredicate
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-! Ordinary permutation-surgery clients, with no graph import in their transitive closure. -/

open Equiv Perm.SelectedOrbits

-- The swapped elements are distinct and both satisfy a genuinely nonconstant predicate.
example (x : Fin 4) : (Equiv.swap (0 : Fin 4) 1 x).val < 2 ↔ x.val < 2 :=
  Equiv.predicate_swap (fun x : Fin 4 => x.val < 2) 0 1 (by decide) x

example : Equiv.swap (0 : Fin 4) 1 0 = 1 ∧ ¬ (2 : Fin 4).val < 2 := by decide

example : Nat.card (OrbitOn (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 0 1)
      (fun x : Fin 4 => x.val < 2)) =
    Nat.card (OrbitOn (Equiv.swap (0 : Fin 4) 1) (fun x : Fin 4 => x.val < 2)) + 1 := by
  simpa using card_orbitOn_swap_mul (Equiv.swap (0 : Fin 4) 1) (fun x => x.val < 2)
    (by decide +kernel) 0 1 (by decide) (by decide +kernel)

example : Equiv.Perm.Insertion.insertAfter (Equiv.refl (Fin 1)) 0 none = some 0 := by decide

open Lean Elab Command in
run_cmd do
  let graphPrefix := `Complexity.Computability.Complexity.Problems.Graph
  for name in (← getEnv).header.moduleNames do
    if graphPrefix.isPrefixOf name then
      throwError "generic permutation client unexpectedly imports graph module {name}"
