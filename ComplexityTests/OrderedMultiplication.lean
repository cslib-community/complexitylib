/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Multiplication

/-! # Native TIMES, overflow rejection, and packed-decoder boundaries -/

@[expose] public section

namespace Cslib.Tests.OrderedMultiplication

open FirstOrder Language Structure Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 2) := ⟨by decide⟩
instance : Fact (2 ≤ 3) := ⟨by decide⟩
instance : Fact (2 ≤ 5) := ⟨by decide⟩
instance : Fact (2 ≤ 256) := ⟨by decide⟩
instance : Fact (2 ≤ 257) := ⟨by decide⟩
instance : Fact (2 ≤ 1000) := ⟨by decide⟩
instance : Fact (2 ≤ 262145) := ⟨by decide⟩

/-- Realization, overflow rejection, packed-witness boundaries, and uniqueness of `multiplication L`
across `Fin 2`, `Fin 3`, `Fin 5`, `Fin 256`, `Fin 257`, `Fin 1000`, and `Fin 262145`. -/
example (z₃ : Fin 3) (z₂₅₇ : Fin 257) (z₁₀₀₀ : Fin 1000) :
    (multiplication L).Realize (![0, 1, 0] : Fin 3 → Fin 2) ∧
    (multiplication L).Realize (![1, 0, 0] : Fin 3 → Fin 2) ∧
    (multiplication L).Realize (![1, 1, 1] : Fin 3 → Fin 2) ∧
    ¬(multiplication L).Realize (![1, 1, 0] : Fin 3 → Fin 2) ∧
    (multiplication L).Realize (![2, 2, 4] : Fin 3 → Fin 5) ∧
    ¬(multiplication L).Realize ![2, 2, z₃] ∧
    (multiplication L).Realize (![255, 1, 255] : Fin 3 → Fin 256) ∧
    (multiplication L).Realize (![256, 1, 256] : Fin 3 → Fin 257) ∧
    (multiplication L).Realize (![256, 0, 0] : Fin 3 → Fin 257) ∧
    ¬(multiplication L).Realize ![256, 2, z₂₅₇] ∧
    (multiplication L).Realize (![300, 3, 900] : Fin 3 → Fin 1000) ∧
    ¬(multiplication L).Realize ![300, 4, z₁₀₀₀] ∧
    (multiplication L).Realize (![511, 511, 261121] : Fin 3 → Fin 262145) ∧
    (∃! z : Fin 1000, (multiplication L).Realize ![300, 3, z]) :=
  ⟨by rw [realize_multiplication]; decide,
    by rw [realize_multiplication]; decide,
    by rw [realize_multiplication]; decide,
    by rw [realize_multiplication]; decide,
    by rw [realize_multiplication]; decide,
    not_realize_multiplication_of_le _ (by change 3 ≤ 4; decide),
    by rw [realize_multiplication]; decide,
    by rw [realize_multiplication]; decide,
    by rw [realize_multiplication]; decide,
    not_realize_multiplication_of_le _ (by change 257 ≤ 512; decide),
    by rw [realize_multiplication]; decide,
    not_realize_multiplication_of_le _ (by change 1000 ≤ 1200; decide),
    by rw [realize_multiplication]; decide,
    existsUnique_multiplication 300 3 (by decide)⟩

/-- The formula composes with ordinary variable relabeling. -/
example (v : Fin 4 → Fin 1000) :
    ((multiplication L).relabel (fun i => i.succ)).Realize v ↔
      (v 1).val * (v 2).val = (v 3).val := by
  rw [Formula.realize_relabel, realize_multiplication]
  rfl

/-- A one-bit field rejects a high set bit even for arbitrary packed words. -/
example (w : Fin 8 → Fin 257) :
    ¬(packedField L (.var (.inl 0)) (fun r => .var (.inr r)) (.var (.inl 1))
      (.var (.inl 2)) (.var (.inl 3))).Realize (Sum.elim (![8, 0, 1, 2] : Fin 4 → Fin 257) w) := by
  rw [realize_packedField _ _ _ _ _ _ (by change 8 * 8 < 257; decide)]
  intro he
  have hb := BitString.readPackedField_lt 8 (fun r => (w r).val) 0 1
  change 2 = BitString.readPackedField 8 (fun r => (w r).val) 0 1 at he
  rw [← he] at hb
  contradiction

end Cslib.Tests.OrderedMultiplication
