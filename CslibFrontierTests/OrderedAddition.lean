/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Addition

/-! # Exact addition on arbitrary canonical universe sizes -/

@[expose] public section

namespace Cslib.Tests.OrderedAddition

open FirstOrder Language Structure Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 2) := ⟨by decide⟩
instance : Fact (2 ≤ 3) := ⟨by decide⟩
instance : Fact (2 ≤ 5) := ⟨by decide⟩
instance : Fact (2 ≤ 9) := ⟨by decide⟩

example : (addition L).Realize (![0, 1, 1] : Fin 3 → Fin 2) := by
  rw [realize_addition]
  decide

/-- Minimum allowed universe: overflow is rejected for every candidate, not wrapped to zero. -/
example (z : Fin 2) : ¬(addition L).Realize ![1, 1, z] := by
  apply not_realize_addition_of_le
  change 2 ≤ 1 + 1
  decide

/-- A non-power-of-two universe includes a carry and its maximum result. -/
example : (addition L).Realize (![1, 1, 2] : Fin 3 → Fin 3) := by
  rw [realize_addition]
  decide

example (z : Fin 3) : ¬(addition L).Realize ![2, 2, z] := by
  apply not_realize_addition_of_le
  change 3 ≤ 2 + 2
  decide

example : (addition L).Realize (![3, 1, 4] : Fin 3 → Fin 5) := by
  rw [realize_addition]
  decide

example (z : Fin 5) : ¬(addition L).Realize ![4, 1, z] := by
  apply not_realize_addition_of_le
  change 5 ≤ 4 + 1
  decide

/-- Three consecutive carries reach bit three in an odd-sized universe. -/
example : (addition L).Realize (![7, 1, 8] : Fin 3 → Fin 9) := by
  rw [realize_addition]
  decide

/-- A carry is killed at a position where both inputs are zero. -/
example : (addition L).Realize (![1, 1, 2] : Fin 3 → Fin 9) := by
  rw [realize_addition]
  decide

example : ¬(addition L).Realize (![1, 1, 6] : Fin 3 → Fin 9) := by
  rw [realize_addition]
  decide

example : (addition L).Realize (![0, 0, 0] : Fin 3 → Fin 3) := by
  rw [realize_addition]
  decide

/-- Relabeling the native formula retains arbitrary free-variable assignments. -/
example (v : Fin 4 → Fin 5) :
    ((addition L).relabel (fun i => i.succ)).Realize v ↔
      (v 1).val + (v 2).val = (v 3).val := by
  rw [Formula.realize_relabel, realize_addition]
  rfl

end Cslib.Tests.OrderedAddition
