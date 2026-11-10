/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.SeedFixing

/-!
# Multi-output seed-fixing clients

A relation-valued two-output example has one bad seed per input but common good seeds.
The boundary example shows why a non-strict counting bound would be insufficient.
-/

namespace CslibFrontierTests.SeedFixing

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Finset

private def seedOutputs : Circuit signature (1 + 2) 2 :=
  Circuit.wiring signature (Fin.natAdd 1)

private def acceptable (x : BitString 1) (y : BitString 2) : Prop :=
  y 1 = true ∨ y 0 ≠ x 0

private instance (x : BitString 1) (y : BitString 2) : Decidable (acceptable x y) :=
  inferInstanceAs (Decidable (y 1 = true ∨ y 0 ≠ x 0))

private theorem seedOutputs_bound : ∀ x : BitString 1,
    2 ^ 1 * #{r : BitString 2 | ¬acceptable x
      (seedOutputs.eval interpretation (Fin.append x r))} < 2 ^ 2 := by
  decide

example : ∃ r : BitString 2, ∀ x : BitString 1,
    acceptable x (seedOutputs.eval interpretation (Fin.append x r)) :=
  seedOutputs.exists_seed_forall acceptable seedOutputs_bound

example : ∃ D : Circuit signature 1 2,
    (∀ x, acceptable x (D.eval interpretation x)) ∧
      D.size ≤ seedOutputs.size + 2 ∧ D.depth ≤ seedOutputs.depth + 1 :=
  exists_circuit_of_card_bad_lt seedOutputs acceptable seedOutputs_bound

private def inputOutput : Circuit signature (1 + 1) 1 :=
  Circuit.wiring signature (fun _ => 0)

example : ∃ D : Circuit signature 1 1, D.Computes interpretation id ∧
    D.size ≤ inputOutput.size + 2 ∧ D.depth ≤ inputOutput.depth + 1 :=
  exists_computes_of_card_bad_lt inputOutput id (by decide)

-- Empty input, seed, and output types still have the unique empty bit string.
example : ∃ r : BitString 0, ∀ x : BitString 0,
    (Circuit.wiring signature (Fin.elim0 : Fin 0 → Fin (0 + 0))).eval
      interpretation (Fin.append x r) = Fin.elim0 := by
  apply Circuit.exists_seed_forall _ (fun _ y => y = Fin.elim0)
  decide

-- At equality, each input can forbid a different seed, so no common good seed exists.
example : (∀ x : BitString 1,
    2 ^ 1 * #{r : BitString 1 | r 0 ≠ x 0} ≤ 2 ^ 1) ∧
      ¬∃ r : BitString 1, ∀ x : BitString 1, r 0 = x 0 := by
  decide

end CslibFrontierTests.SeedFixing
