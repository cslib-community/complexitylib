/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.MassProduction.ConstantCopies
import CslibFrontier.Computability.Circuit.Boolean.Lookup
import Mathlib.Tactic.GCongr

/-!
# Mass production of a constant number of copies

The client reads a table `F` on `L` inputs at three addresses given directly by the input, and
returns the exclusive or of the three values. Eventually in `L`, uniformly in `F`, this costs at
most `(1 + 1 / P) 2 ^ L / L` gates plus a constant: the addresses are wiring, and the exclusive
or of three bits is a local map.
-/

namespace CslibFrontierTests.MassProduction.ConstantCopies

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.MassProduction Filter Finset

/-- The exclusive or of the last three of `n + 3` inputs. -/
private def xor3 {n : ℕ} (y : Fin (n + 3) → Bool) : Fin 1 → Bool := fun _ =>
  y (Fin.natAdd n 0) ^^ y (Fin.natAdd n 1) ^^ y (Fin.natAdd n 2)

-- Three table reads and their exclusive or: the identity addresses cost nothing, and the
-- exclusive or of three inputs costs at most `73` gates.
example (P : ℕ) :
    ∀ᶠ L in atTop, ∀ F : BooleanFunction L,
      P * L * complexity interpretation
          (fun x => xor3 (Fin.append x (directProduct F 3 (x ∘ id)))) ≤
        (P + 1) * 2 ^ L + P * L * 73 := by
  filter_upwards [eventually_mul_complexity_table_le P 3] with L hL F
  have h0 : complexity interpretation (fun x : Fin (3 * L) → Bool => x ∘ id) = 0 :=
    complexity_wiring id
  have h3 : complexity interpretation (xor3 (n := 3 * L)) ≤ 73 :=
    complexity_le_mul_of_forall_dependsOn (t := 3) _ fun _ =>
      ⟨{Fin.natAdd _ 0, Fin.natAdd _ 1, Fin.natAdd _ 2}, card_le_three, fun x y h => by
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at h
        simp only [xor3, h _ (Or.inl rfl), h _ (Or.inr (Or.inl rfl)), h _ (Or.inr (Or.inr rfl))]⟩
  refine (hL F (fun x => x ∘ id) xor3).trans ?_
  rw [h0, zero_add]
  gcongr

end CslibFrontierTests.MassProduction.ConstantCopies
