/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: local-only (tests of Complexity.Foundations.Data.BitString.Support)

public import Complexity.Foundations.Data.BitString.Support

/-! # Unit tests for `Cslib.BitString.supportOfList` -/

namespace ComplexityTests.BitString.Support

open Cslib.BitString

-- 1. Empty, exact-length, padded-short, and truncated-long words, plus `mem_supportOfList`.
example : supportOfList 0 [true, false] = ∅ ∧
    supportOfList 4 [true, false, true, false] = ({0, 2} : Finset (Fin 4)) ∧
    supportOfList 4 [true] = ({0} : Finset (Fin 4)) ∧
    supportOfList 2 [false, true, true, true] = ({1} : Finset (Fin 2)) ∧
    ((⟨2, by decide⟩ : Fin 4) ∈ supportOfList 4 [true, false, true, false]) ∧
    ((⟨1, by decide⟩ : Fin 4) ∉ supportOfList 4 [true, false, true, false]) :=
  ⟨by decide, by decide, by decide, by decide, mem_supportOfList.mpr rfl,
    mt mem_supportOfList.mp (by decide)⟩

-- 2. Round-trips `supportOfList_ofFn_decide` and `ofFn_decide_mem_supportOfList` + length control.
example :
    supportOfList 4 (List.ofFn fun i : Fin 4 => decide (i ∈ ({1, 3} : Finset (Fin 4)))) = {1, 3} ∧
    (List.ofFn fun i : Fin 3 => decide (i ∈ supportOfList 3 [false, true, true])) =
      [false, true, true] ∧
    (List.ofFn fun i : Fin 2 => decide (i ∈ supportOfList 2 [true])) ≠ [true] :=
  ⟨supportOfList_ofFn_decide {1, 3}, ofFn_decide_mem_supportOfList rfl, by decide⟩

-- 3. `supportOfList_injective_of_length` and `card_supportOfList_of_length` + length controls.
example {w : List Bool} (hw : w.length = 3)
    (h : supportOfList 3 w = supportOfList 3 [true, false, true]) :
    w = [true, false, true] ∧ (supportOfList 3 w).card = 2 ∧
      (supportOfList 2 [true] = supportOfList 2 [true, false] ∧ [true] ≠ [true, false]) ∧
      (supportOfList 2 [true, true, true]).card ≠ [true, true, true].count true :=
  ⟨supportOfList_injective_of_length hw rfl h,
    by rw [card_supportOfList_of_length hw, supportOfList_injective_of_length hw rfl h]; rfl,
    by decide, by decide⟩

end ComplexityTests.BitString.Support
