/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory

/-!
# Charged native return and term-advance transitions

## Main results

* `PrunedQuery.exec_pop`: return to the parent's accumulation phase or terminate the root.
* `PrunedQuery.exec_advance`: store the incremented term counter in the actual parent frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers changed by a return transition. -/
def PopLocal (i : Fin registers) : Prop := i = active ∨ i = level ∨ i = mode

instance (i : Fin registers) : Decidable (PopLocal i) :=
  inferInstanceAs (Decidable (i = active ∨ i = level ∨ i = mode))

private theorem pop_preserves (i : Fin registers) : ¬PopLocal i → pop.Preserves i := by
  decide +kernel +revert

/-- The return decision is the program's real comparison with zero. Both branches preserve
memory and all registers outside the three controller fields. -/
theorem exec_pop {w : ℕ} (x : Data registers) (h0 : x.regs nil = 0)
    (h1 : x.regs one = 1) (hw : Fits w (x.regs level + 2)) :
    ∃ y, ExecWithin w pop x y 4 ∧ y.mem = x.mem ∧
      y.regs level = (if x.regs level = 0 then 0 else x.regs level - 1) ∧
      y.regs mode = (if x.regs level = 0 then x.regs mode else 2) ∧
      y.regs active = (if x.regs level = 0 then 0 else x.regs active) ∧
      (∀ i, ¬PopLocal i → y.regs i = x.regs i) := by
  have h2 : Fits w 2 := hw.of_le (by omega)
  have hd : Fits w (x.regs level - 1) := hw.of_le (by omega)
  by_cases hroot : x.regs level = 0
  · let y := x.set active 0
    have he : ExecWithin w pop x y 2 := by
      ram_eval [pop, y, hroot, h0]
    refine ⟨y, he.mono (by decide), rfl, ?_, ?_, ?_,
      fun i hi => he.regs_eq (pop_preserves i hi)⟩
    all_goals simp +decide [y, hroot, active, level, mode]
  · let y := (x.set level (x.regs level - 1)).set mode 2
    have he : ExecWithin w pop x y 4 := by
      ram_eval [pop, y, hroot, h0, h1, h2, hd, level, mode, one, Fin.mk.injEq]
    refine ⟨y, he, rfl, ?_, ?_, ?_, fun i hi => he.regs_eq (pop_preserves i hi)⟩
    all_goals simp +decide [y, hroot, active, level, mode]

/-- Registers changed by advancing and storing a term counter. -/
def AdvanceLocal (i : Fin registers) : Prop := i = term ∨ i = address ∨ i = mode

instance (i : Fin registers) : Decidable (AdvanceLocal i) :=
  inferInstanceAs (Decidable (i = term ∨ i = address ∨ i = mode))

private theorem advance_preserves (i : Fin registers) :
    ¬AdvanceLocal i → advance.Preserves i := by decide +kernel +revert

/-- Store a term already in its register and switch to dispatch, charging all four operations. -/
theorem exec_storeTerm {w : ℕ} (x : Data registers) (h1 : x.regs one = 1)
    (h4 : x.regs frameWidth = 4) (hf : Fits w (x.regs frame + 4)) :
    ∃ y, ExecWithin w storeTerm x y 4 ∧ y.regs mode = 1 ∧
      y.mem = Function.update x.mem (x.regs frame + 3) (x.regs term) ∧
      (∀ i, i ≠ address → i ≠ mode → y.regs i = x.regs i) := by
  have hmode : Fits w 1 := hf.of_le (by omega)
  have hadd : Fits w (x.regs frame + 3) := hf.of_le (by omega)
  let y := ((((x.set address (x.regs frame + 4)).set address (x.regs frame + 3)).write
    (x.regs frame + 3) (x.regs term)).set mode 1)
  have hsub : x.regs frame + 4 - 1 = x.regs frame + 3 := by omega
  have he : ExecWithin w storeTerm x y 4 := by
    ram_eval [storeTerm, y, h1, h4, hf, hmode, hadd, hsub, address, mode, one,
      frame, frameWidth, term, Fin.mk.injEq]
  refine ⟨y, he, by simp [y], rfl, ?_⟩
  intro i ha hm
  exact he.regs_eq (by decide +kernel +revert)

/-- The term increment, frame-word address computation, store and phase assignment take five
instructions. Only the fourth frame word changes in memory. -/
theorem exec_advance {w : ℕ} (x : Data registers) (h1 : x.regs one = 1)
    (h4 : x.regs frameWidth = 4) (ht : Fits w (x.regs term + 1))
    (hf : Fits w (x.regs frame + 4)) :
    ∃ y, ExecWithin w advance x y 5 ∧ y.regs term = x.regs term + 1 ∧
      y.regs mode = 1 ∧
      y.mem = Function.update x.mem (x.regs frame + 3) (x.regs term + 1) ∧
      (∀ i, ¬AdvanceLocal i → y.regs i = x.regs i) := by
  let z := x.set term (x.regs term + 1)
  have hpre : ExecWithin w (ram[ term ← term + one ]) x z 1 := by
    ram_eval [z, h1, ht]
  obtain ⟨y, hy, hm, hmem, hreg⟩ := exec_storeTerm z
    (by simpa +decide [z, one, term] using h1)
    (by simpa +decide [z, frameWidth, term] using h4)
    (by simpa +decide [z, frame, term] using hf)
  have he : ExecWithin w advance x y 5 := hpre.seq hy
  refine ⟨y, he, ?_, hm, ?_, fun i hi => he.regs_eq (advance_preserves i hi)⟩
  · simpa [z] using hreg term (by decide) (by decide)
  · simpa +decide [z, frame, term] using hmem

private theorem clearFinish_preserves (i : Fin registers) :
    ¬AdvanceLocal i → clearValuesFinish.Preserves i := by decide +kernel +revert

/-- Initialization uses the same actual frame store as advancement, with a zero term counter. -/
theorem exec_clearValuesFinish {w : ℕ} (x : Data registers) (h1 : x.regs one = 1)
    (h4 : x.regs frameWidth = 4) (hf : Fits w (x.regs frame + 4)) :
    ∃ y, ExecWithin w clearValuesFinish x y 5 ∧ y.regs term = 0 ∧ y.regs mode = 1 ∧
      y.mem = Function.update x.mem (x.regs frame + 3) 0 ∧
      (∀ i, ¬AdvanceLocal i → y.regs i = x.regs i) := by
  let z := x.set term 0
  have hpre : ExecWithin w (ram[ term ← #0 ] : Code .standard registers) x z 1 := by
    ram_eval [z]
  obtain ⟨y, hy, hm, hmem, hreg⟩ := exec_storeTerm z
    (by simpa +decide [z, one, term] using h1)
    (by simpa +decide [z, frameWidth, term] using h4)
    (by simpa +decide [z, frame, term] using hf)
  have he : ExecWithin w clearValuesFinish x y 5 := hpre.seq hy
  refine ⟨y, he, ?_, hm, ?_, fun i hi => he.regs_eq (clearFinish_preserves i hi)⟩
  · simpa [z] using hreg term (by decide) (by decide)
  · simpa +decide [z, frame, term] using hmem

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
