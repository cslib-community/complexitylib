/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingProgram
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingEntries

/-!
# Native frontend descriptor loads

The controller executes all six memory reads and the fuel copy. The semantic entry is obtained
from the existing frontend output relation, including empty compact arrays.

## Main results

* `loadRoot_exec`: exact native descriptor loading, charged execution and memory/register frame.

These representation and native execution proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- A descriptor load changes only the seven current-record slots and its address scratch. -/
theorem loadRoot_preserves : ∀ i : Fin 128,
    (i.val < 64 ∨ 71 ≤ i.val) → i ≠ address → loadRoot.Preserves i := by decide

/-- Execute all descriptor arithmetic, six native memory reads and the runtime fuel copy. -/
theorem loadRoot_exec {w U f t : ℕ} {l : Frontend.Layout} {rs : List (ℕ × ℕ)}
    (x : Data 128) (hx : x.Bounded w) (ht : t < l.count)
    (hc : x.regs current = t) (hd : x.regs descriptors = l.descriptors)
    (hf : x.regs levels = f) (hs : x.regs stride = 6) (ho : x.regs one = 1)
    (hfit : Fits w (l.descriptors + 6 * t + 5))
    (houtput : Frontend.Output l U rs x.mem) :
    ∃ y, Exec w loadRoot x y 14 ∧ (entry l U f rs t).Loaded y ∧ y.mem = x.mem ∧
      ∀ i : Fin 128, (i.val < 64 ∨ 71 ≤ i.val) → i ≠ address → y.regs i = x.regs i := by
  let a := l.descriptors + 6 * t
  let y := x |>.set address (t * 6) |>.set address a |>.set (Traversal.slot 0) f
    |>.set (Traversal.slot 2) (x.mem a) |>.set address (a + 1)
    |>.set (Traversal.slot 1) (x.mem (a + 1)) |>.set address (a + 2)
    |>.set (Traversal.slot 4) (x.mem (a + 2)) |>.set address (a + 3)
    |>.set (Traversal.slot 3) (x.mem (a + 3)) |>.set address (a + 4)
    |>.set (Traversal.slot 6) (x.mem (a + 4)) |>.set address (a + 5)
    |>.set (Traversal.slot 5) (x.mem (a + 5))
  have ha (k : ℕ) (hk : k ≤ 5) : Fits w (a + k) := hfit.of_le (by dsimp only [a]; omega)
  have ha' (k : ℕ) (hk : k ≤ 5) : Fits w (l.descriptors + (t * 6 + k)) :=
    hfit.of_le (by omega)
  have hbase : Fits w (l.descriptors + t * 6) := by
    simpa only [Nat.add_zero] using ha' 0 (by decide)
  have hmul : Fits w (t * 6) := hfit.of_le (by omega)
  have hF : Fits w f := hf ▸ hx.1 levels
  have he : Exec w loadRoot x y 14 := by
    ram_eval [loadRoot, y, a, hc, hd, hf, hs, ho, hmul, ha 0 (by decide),
      ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
      ha 5 (by decide), hF, hx.2, current, descriptors, levels, stride, one, address,
      Traversal.slot, Nat.mul_comm, Nat.add_assoc, hbase,
      ha' 1 (by decide), ha' 2 (by decide), ha' 3 (by decide), ha' 4 (by decide),
      ha' 5 (by decide), Fin.val_zero, Fin.val_one, Fin.val_two]
  refine ⟨y, he, ?_, rfl, fun i hi hj => he.within.regs_eq (loadRoot_preserves i hi hj)⟩
  have hread (j : Fin 3) := houtput (3 * t + j.val) (entry_slot ht j)
  have h₀ := hread 0
  have h₁ := hread 1
  have h₂ := hread 2
  have ha₀ : l.descriptors + 2 * (3 * t + 0) = a := by dsimp only [a]; omega
  have ha₁ : l.descriptors + 2 * (3 * t + 1) = a + 2 := by dsimp only [a]; omega
  have ha₂ : l.descriptors + 2 * (3 * t + 2) = a + 4 := by dsimp only [a]; omega
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, ha₀, ha₁, ha₂] at h₀ h₁ h₂
  refine ⟨by simp +decide [y, entry, Traversal.slot, address], ?_, ?_⟩
  · intro j
    fin_cases j <;> simpa +decide [y, entry, Traversal.arraySource, Traversal.slot,
      address, Nat.add_assoc] using (by first | exact h₀.2.1 | exact h₁.2.1 | exact h₂.2.1)
  · intro j
    fin_cases j <;> simpa +decide [y, entry, Traversal.arrayLength, Traversal.slot,
      address, List.length_map, Nat.add_assoc] using
        (by first | exact h₀.1 | exact h₁.1 | exact h₂.1)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
