/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.BitSum

/-! # Native Bit Sum and exact-shift boundaries -/

@[expose] public section

namespace Cslib.Tests.OrderedBitSum

open FirstOrder Language Structure Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 2) := ⟨by decide⟩
instance : Fact (2 ≤ 3) := ⟨by decide⟩
instance : Fact (2 ≤ 5) := ⟨by decide⟩
instance : Fact (2 ≤ 8) := ⟨by decide⟩
instance : Fact (2 ≤ 9) := ⟨by decide⟩
instance : Fact (2 ≤ 256) := ⟨by decide⟩
instance : Fact (2 ≤ 257) := ⟨by decide⟩
instance : Fact (2 ≤ 512) := ⟨by decide⟩
instance : Fact (2 ≤ 513) := ⟨by decide⟩

/-- Realization of `bitSum L` across `Fin 2`, `Fin 3`, `Fin 9`, `Fin 256`, `Fin 257`, `Fin 512`, and
`Fin 513`, together with `shiftLeft L` on `Fin 8`. -/
example :
    (bitSum L).Realize (![0, 0] : Fin 2 → Fin 2) ∧
    (bitSum L).Realize (![1, 1] : Fin 2 → Fin 2) ∧
    ¬(bitSum L).Realize (![1, 0] : Fin 2 → Fin 2) ∧
    (bitSum L).Realize (![2, 1] : Fin 2 → Fin 3) ∧
    (bitSum L).Realize (![7, 3] : Fin 2 → Fin 9) ∧
    (bitSum L).Realize (![8, 1] : Fin 2 → Fin 9) ∧
    (bitSum L).Realize (![255, 8] : Fin 2 → Fin 256) ∧
    (bitSum L).Realize (![256, 1] : Fin 2 → Fin 257) ∧
    (bitSum L).Realize (![511, 9] : Fin 2 → Fin 512) ∧
    (bitSum L).Realize (![512, 1] : Fin 2 → Fin 513) ∧
    ¬(bitSum L).Realize (![511, 8] : Fin 2 → Fin 512) ∧
    ¬(shiftLeft L (.var 0) (.var 1) (.var 2)).Realize (![4, 7, 0] : Fin 3 → Fin 8) ∧
    (shiftLeft L (.var 0) (.var 1) (.var 2)).Realize (![0, 7, 0] : Fin 3 → Fin 8) :=
  ⟨by rw [realize_bitSum]; decide,
    by rw [realize_bitSum]; decide,
    by rw [realize_bitSum]; decide,
    by rw [realize_bitSum]; decide,
    by rw [realize_bitSum]; decide,
    by rw [realize_bitSum]; decide,
    by rw [realize_bitSum]; decide,
    by rw [realize_bitSum]; decide,
    by rw [realize_bitSum]; decide,
    by rw [realize_bitSum]; decide,
    by rw [realize_bitSum]; decide,
    by rw [realize_shiftLeft]; decide,
    by rw [realize_shiftLeft]; decide⟩

/-- Composition with arbitrary free-variable assignments uses the same native formula. -/
example (v : Fin 3 → Fin 257) :
    ((bitSum L).relabel (fun i => i.succ)).Realize v ↔
      (v 2).val = (v 1).val.bitIndices.length := by
  rw [Formula.realize_relabel, realize_bitSum]
  rfl

/-- Fixed syntactic numerals do not assume that the universe contains them. -/
example (x : Fin 2) : ¬(natEq L 256 (.var ())).Realize (fun _ => x) := by
  rw [realize_natEq]
  have := x.isLt
  change ¬x.val = 256
  lia

/-- A positive shift that leaves the universe has no output. -/
example (z : Fin 5) :
    ¬(shiftLeft L (.var 0) (.var 1) (.var 2)).Realize (![3, 1, z] : Fin 3 → Fin 5) := by
  rw [realize_shiftLeft]
  have := z.isLt
  change ¬6 = z.val
  lia

/-- A leaf decoder constrains high bits even when its packed words are arbitrary. -/
example (w : Fin 8 → ℕ) : ¬BitSum.EncodesNode 1 8 w 0 0 3 := by
  intro h
  have := ((h 1).mp (by decide)).1
  lia

end Cslib.Tests.OrderedBitSum
