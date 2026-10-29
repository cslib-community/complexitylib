/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Frame
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Leaf

/-!
# The terminal case of the actual pruned-query controller

## Main results

* `PrunedQuery.exec_leafStep`: load the stored frame, select the leaf phase and return.
* `PrunedQuery.exec_controller_leaf`: prepend this real iteration to the controller's
  remaining execution, with its charged loop test.

These use the existing native `ExecWithin` semantics throughout. The continuation is a
conclusion of the execution proof, rather than a hypothesis supplying a solver or its cost.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Registers written by frame loading and a terminal controller phase. -/
def LeafStepLocal (i : Fin registers) : Prop := LoadFrameLocal i ∨ LeafReturnLocal i

instance (i : Fin registers) : Decidable (LeafStepLocal i) :=
  inferInstanceAs (Decidable (LoadFrameLocal i ∨ LeafReturnLocal i))

/-- The actual controller reads its frame and takes both real entry/leaf comparisons.
The only possible store is the requested product at this depth's value-row base. -/
theorem exec_leafStep {w p : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (hab : GenericRAM.Signed.Fits w (a * b))
    (x : Data registers) (h0 : x.regs nil = 0) (h1 : x.regs one = 1)
    (h4 : x.regs frameWidth = 4) (hm : x.regs mode = 0)
    (hd : x.regs level = x.regs inputDepth)
    (hpref : x.mem (x.regs frames + 4 * x.regs level + 1) = p)
    (hleft : x.mem (x.regs arrayA + p) = encode a)
    (hright : x.mem (x.regs arrayB + p) = encode b)
    (hw : Fits (w + 2) (x.regs frames + 4 * (x.regs level + 1) + x.regs lists +
      x.regs values + (x.regs level + 1) * x.regs span + x.regs level +
      x.regs arrayA + p + x.regs arrayB + p + 12)) :
    ∃ y, ExecWithin (w + 2) step x y 43 ∧
      y.mem = (if x.mem (x.regs frames + 4 * x.regs level) = 0 then x.mem else
        Function.update x.mem (x.regs values + x.regs level * x.regs span)
          (encode (a * b))) ∧
      y.regs level = (if x.regs level = 0 then 0 else x.regs level - 1) ∧
      y.regs mode = (if x.regs level = 0 then 0 else 2) ∧
      y.regs active = (if x.regs level = 0 then 0 else x.regs active) ∧
      (∀ i, ¬LeafStepLocal i → y.regs i = x.regs i) := by
  obtain ⟨u, hu, humem, _, huc, hup, _, _, _, huv, _, _, _, hureg⟩ :=
    exec_loadFrame x h1 h4 (hw.of_le (by omega))
  have fixed (i : Fin registers) (hi : ¬LoadFrameLocal i) : u.regs i = x.regs i :=
    hureg i hi
  have hu0 := (fixed nil (by decide)).trans h0
  have hu1 := (fixed one (by decide)).trans h1
  have hud := fixed level (by decide)
  have hum := (fixed mode (by decide)).trans hm
  have hua := fixed active (by decide)
  have huA := fixed arrayA (by decide)
  have huB := fixed arrayB (by decide)
  have hup' : u.regs leafPrefix = p := hup.trans hpref
  obtain ⟨y, hy, hymem, hyl, hym, hya, hyreg⟩ := exec_leaf ha hb hab u hu0 hu1
    (by simpa only [humem, huA, hup'] using hleft)
    (by simpa only [humem, huB, hup'] using hright)
    (hw.of_le (by rw [huA, hup']; omega))
    (hw.of_le (by rw [huB, hup']; omega))
    (hw.of_le (by rw [hud]; omega))
  have hentry : ExecWithin (w + 2) enter u y 25 :=
    hy.branch_pos (by simpa only [Cond.holds_eq, hud, fixed inputDepth (by decide)] using hd)
  have hbranch : ExecWithin (w + 2)
      (ram[ if mode = nil then [ ⟪enter⟫ ] else [
        if mode = one then [ ⟪dispatch⟫ ] else [ ⟪accumulate⟫ ] ] ]) u y 26 :=
    hentry.branch_pos (by simp only [Cond.holds_eq, hum, hu0])
  refine ⟨y, hu.seq hbranch, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [huc, huv, humem] using hymem
  · simpa only [hud] using hyl
  · simpa only [hud, hum] using hym
  · simpa only [hud, hua] using hya
  · intro i hi
    exact (hyreg i (fun h => hi (Or.inr h))).trans
      (hureg i (fun h => hi (Or.inl h)))

/-- A terminal node is one actual iteration of the existing native loop. Its 43 body
instructions plus the two loop instructions are charged before any continuation. -/
theorem exec_controller_leaf {w p : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (hab : GenericRAM.Signed.Fits w (a * b))
    (x : Data registers) (h0 : x.regs nil = 0) (h1 : x.regs one = 1)
    (h4 : x.regs frameWidth = 4) (hm : x.regs mode = 0)
    (hd : x.regs level = x.regs inputDepth) (hactive : x.regs active = 1)
    (hpref : x.mem (x.regs frames + 4 * x.regs level + 1) = p)
    (hleft : x.mem (x.regs arrayA + p) = encode a)
    (hright : x.mem (x.regs arrayB + p) = encode b)
    (hw : Fits (w + 2) (x.regs frames + 4 * (x.regs level + 1) + x.regs lists +
      x.regs values + (x.regs level + 1) * x.regs span + x.regs level +
      x.regs arrayA + p + x.regs arrayB + p + 12)) :
    ∃ y, y.mem = (if x.mem (x.regs frames + 4 * x.regs level) = 0 then x.mem else
        Function.update x.mem (x.regs values + x.regs level * x.regs span)
          (encode (a * b))) ∧
      y.regs level = (if x.regs level = 0 then 0 else x.regs level - 1) ∧
      y.regs mode = (if x.regs level = 0 then 0 else 2) ∧
      y.regs active = (if x.regs level = 0 then 0 else 1) ∧
      (∀ i, ¬LeafStepLocal i → y.regs i = x.regs i) ∧
      ∀ z U, ExecWithin (w + 2) controller y z U →
        ExecWithin (w + 2) controller x z (45 + U) := by
  obtain ⟨y, hy, hmem, hyl, hym, hya, hreg⟩ :=
    exec_leafStep ha hb hab x h0 h1 h4 hm hd hpref hleft hright hw
  refine ⟨y, hmem, hyl, hym, by simpa only [hactive] using hya, hreg, ?_⟩
  intro z U hz
  have he := ExecWithin.loop_iter (by simp only [Cond.holds_lt, h0, hactive]; decide) hy hz
  exact he.mono (by omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
