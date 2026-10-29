/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory

/-!
# Charged consumption of a returned child value

## Main results

* `PrunedQuery.exec_addValue`: compute the child suffix address, load both signed words, call
  the existing signed-add kernel, and store the sum at the parent query address.

The instruction bound includes all indexed accesses and the native arithmetic kernel.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The signed workspace and two address-calculation registers used by one accumulation. -/
def AddValueLocal (i : Fin registers) : Prop := i.val < 9 ∨ i = address ∨ i = suffix

instance (i : Fin registers) : Decidable (AddValueLocal i) :=
  inferInstanceAs (Decidable (i.val < 9 ∨ i = address ∨ i = suffix))

private theorem addValue_preserves (i : Fin registers) :
    ¬AddValueLocal i → addValue.Preserves i := by decide +kernel +revert

/-- All twenty-two instructions are native standard-basis operations. Both operands must fit
the source signed width; their sum is computed exactly by the existing two-extra-bit kernel. -/
theorem exec_addValue {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (x : Data registers) (q : ℕ)
    (hq : x.regs query = q) (h10 : x.regs ten = 10)
    (hleft : x.mem (x.regs valueBase + q) = encode a)
    (hright : x.mem (x.regs childValues + q / 10) = encode b)
    (hp : Fits (w + 2) (x.regs valueBase + q))
    (hc : Fits (w + 2) (x.regs childValues + q / 10)) :
    ∃ y, ExecWithin (w + 2) addValue x y 22 ∧
      y.mem = Function.update x.mem (x.regs valueBase + q) (encode (a + b)) ∧
      (∀ i, ¬AddValueLocal i → y.regs i = x.regs i) := by
  let z := (((((x.set suffix (q / 10)).set address (x.regs valueBase + q)).set
    left (encode a)).set address (x.regs childValues + q / 10)).set right (encode b))
  have hquot : Fits (w + 2) (q / 10) := hc.of_le (by omega)
  have hload : ExecWithin (w + 2) addValueLoad x z 5 := by
    ram_eval [addValueLoad, z, hq, h10, hleft, hright, hp, hc, hquot, suffix, address,
      valueBase, query, ten, childValues, left, right, Fin.mk.injEq]
  obtain ⟨u, hu, hsum, hframe⟩ := Signed.exec_add (r := 87) ha hb z
    (by simp +decide [z, left, right, address]) (by simp [z])
  have hreg (i : Fin registers) (hi : 9 ≤ i.val) (hs : i ≠ suffix) (hd : i ≠ address) :
      u.regs i = x.regs i := by
    rw [hframe.2 i (Or.inr hi)]
    have hl : i ≠ left := by intro he; subst he; exact Nat.not_le_of_lt (by decide) hi
    have hr : i ≠ right := by intro he; subst he; exact Nat.not_le_of_lt (by decide) hi
    simp only [z, Data.set_regs, Function.update_of_ne hr, Function.update_of_ne hd,
      Function.update_of_ne hl, Function.update_of_ne hs]
  have huv := hreg valueBase (by decide) (by decide) (by decide)
  have huq := (hreg query (by decide) (by decide) (by decide)).trans hq
  have hsum' : u.regs result = encode (a + b) := hsum
  let y := (u.set address (x.regs valueBase + q)).write
    (x.regs valueBase + q) (encode (a + b))
  have hstore : ExecWithin (w + 2) addValueStore u y 2 := by
    ram_eval [addValueStore, y, huv, huq, hsum', hp, result, address, Fin.mk.injEq]
  have he : ExecWithin (w + 2) addValue x y 22 := hload.seq (hu.seq hstore)
  refine ⟨y, he, ?_, fun i hi => he.regs_eq (addValue_preserves i hi)⟩
  simpa only [y, Data.write_mem, Data.set_mem, z] using
    congrArg (fun mem => Function.update mem (x.regs valueBase + q) (encode (a + b))) hframe.1

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
