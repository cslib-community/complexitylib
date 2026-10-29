/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalProgram

/-!
# Native preparation of the three Chan–He child records

The third child is pushed first. Original descriptors are retained above the stack dispatcher
and restored before replacing another column. All descriptor moves and the fuel decrement are
native instructions; the same finite code is used at every recursion level.

## Main definitions

* `thirdState`, `secondState`, `firstState`: exact states after the native child-argument blocks.
* `childWords`: the seven actual words of one child record, in its pop order.

## Main results

* `prepareThird_exec`, `prepareSecond_exec`, `prepareFirst_exec`: charged native argument blocks.

The native stack controller and proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- Save both descriptors needed for restoration and prepare the third child. -/
def thirdState (x : Data 128) : Data 128 :=
  ((((((x.set (slot 0) (x.regs (slot 0) - 1)).set (original 0) (x.regs (slot 3))).set
    (original 1) (x.regs (slot 4))).set (original 2) (x.regs (slot 5))).set
    (original 3) (x.regs (slot 6))).set (slot 5) (x.regs (heavyBase 2))).set
    (slot 6) (x.regs (heavyLength 2))

/-- Restore the third original column and prepare the second child. -/
def secondState (x : Data 128) : Data 128 :=
  (((x.set (slot 5) (x.regs (original 2))).set (slot 6) (x.regs (original 3))).set
    (slot 3) (x.regs (heavyBase 1))).set (slot 4) (x.regs (heavyLength 1))

/-- Restore the second original column and prepare the first child. -/
def firstState (x : Data 128) : Data 128 :=
  (((x.set (slot 3) (x.regs (original 0))).set (slot 4) (x.regs (original 1))).set
    (slot 1) (x.regs (heavyBase 0))).set (slot 2) (x.regs (heavyLength 0))

/-- Exact child-record serialization. Only the selected column is replaced by its heavy output. -/
def childWords (x : Data 128) (j : Fin 3) : List ℕ :=
  [x.regs (slot 0) - 1,
    if j = 0 then x.regs (heavyBase 0) else x.regs (slot 1),
    if j = 0 then x.regs (heavyLength 0) else x.regs (slot 2),
    if j = 1 then x.regs (heavyBase 1) else x.regs (slot 3),
    if j = 1 then x.regs (heavyLength 1) else x.regs (slot 4),
    if j = 2 then x.regs (heavyBase 2) else x.regs (slot 5),
    if j = 2 then x.regs (heavyLength 2) else x.regs (slot 6)]

/-- Every child occupies exactly one seven-word native record. -/
theorem length_childWords (x : Data 128) (j : Fin 3) : (childWords x j).length = 7 := rfl

/-- The fuel subtraction and all six descriptor copies cost seven native instructions. -/
theorem prepareThird_exec {w : ℕ} (x : Data 128) (hx : x.Bounded w) (hone : x.regs one = 1) :
    Exec w prepareThird x (thirdState x) 7 := by
  have hfit : Fits w (x.regs (slot 0) - 1) := (hx.1 (slot 0)).of_le (Nat.sub_le _ _)
  dsimp only [slot, one] at hfit hone
  ram_eval [prepareThird, thirdState, slot, one, original, heavyBase, heavyLength, hone, hfit]

/-- Restoring the third column and replacing the second costs four native copies. -/
theorem prepareSecond_exec {w : ℕ} (x : Data 128) :
    Exec w prepareSecond x (secondState x) 4 := by
  ram_eval [prepareSecond, secondState, slot, original, heavyBase, heavyLength]

/-- Restoring the second column and replacing the first costs four native copies. -/
theorem prepareFirst_exec {w : ℕ} (x : Data 128) :
    Exec w prepareFirst x (firstState x) 4 := by
  ram_eval [prepareFirst, firstState, slot, original, heavyBase, heavyLength]

private theorem thirdState_comap (x : Data 128) :
    (thirdState x).comap registers = x.comap registers := by
  ext i
  · fin_cases i <;> simp +decide [thirdState, Data.comap, Data.set, slot, original, registers]
  · rfl

private theorem secondState_comap (x : Data 128) :
    (secondState x).comap registers = x.comap registers := by
  ext i
  · fin_cases i <;> simp +decide [secondState, Data.comap, Data.set, slot, registers]
  · rfl

private theorem firstState_comap (x : Data 128) :
    (firstState x).comap registers = x.comap registers := by
  ext i
  · fin_cases i <;> simp +decide [firstState, Data.comap, Data.set, slot, registers]
  · rfl

/-- Child pushes preserve every persistent controller parameter outside the record and stack. -/
theorem pushChildren_preserves : ∀ i : Fin 128,
    ((71 ≤ i.val ∧ i.val < 96) ∨ 109 ≤ i.val) → pushChildren.Preserves i := by decide

private def words (x : Data 128) : List ℕ :=
  [x.regs (slot 0), x.regs (slot 1), x.regs (slot 2), x.regs (slot 3),
    x.regs (slot 4), x.regs (slot 5), x.regs (slot 6)]

/-- All three child records are pushed by native instructions in reverse order. The resulting
top-first stack contains first, second, third, followed by the original pending suffix. -/
theorem pushChildren_exec {w base capacity : ℕ} (x : Data 128) (vs : List ℕ)
    (hx : x.Bounded w) (hone : x.regs one = 1) (h2 : Fits w 2)
    (hcap : Fits w (base + capacity))
    (hr : Stack.Rep w base capacity vs (x.comap registers))
    (hcapacity : 21 + vs.length ≤ capacity) :
    ∃ y, Exec w pushChildren x y 207 ∧
      Stack.Rep w base capacity (childWords x 0 ++ childWords x 1 ++ childWords x 2 ++ vs)
        (y.comap registers) ∧
      Modifies (Stack.footprint base capacity) x.mem y.mem ∧
      ∀ i, ((71 ≤ i.val ∧ i.val < 96) ∨ 109 ≤ i.val) → y.regs i = x.regs i := by
  let a := thirdState x
  have ha := prepareThird_exec x hx hone
  have hra : Stack.Rep w base capacity vs (a.comap registers) := by
    simpa only [a, thirdState_comap] using hr
  obtain ⟨b, hb, hrb, hfb, hpb⟩ := pushFrame_exec a vs h2 hcap hra
    (fun i => (ha.bounded hx).1 (slot i)) (by omega)
  have hwa : words a = childWords x 2 := by
    simp +decide [words, a, thirdState, childWords, Data.set, slot, original,
      heavyBase, heavyLength]
  change Stack.Rep w base capacity (words a ++ vs) (b.comap registers) at hrb
  rw [hwa] at hrb
  let c := secondState b
  have hc := prepareSecond_exec (w := w) b
  have hrc : Stack.Rep w base capacity (childWords x 2 ++ vs) (c.comap registers) := by
    simpa only [c, secondState_comap] using hrb
  obtain ⟨d, hd, hrd, hfd, hpd⟩ := pushFrame_exec c (childWords x 2 ++ vs) h2 hcap hrc
    (fun i => (hc.bounded (hb.bounded (ha.bounded hx))).1 (slot i))
    (by simp only [List.length_append, length_childWords]; omega)
  have hwc : words c = childWords x 1 := by
    simp +decide [words, c, secondState, hpb, Outside, a, thirdState, childWords, Data.set,
      slot, original, heavyBase, heavyLength]
  change Stack.Rep w base capacity (words c ++ (childWords x 2 ++ vs)) (d.comap registers) at hrd
  rw [hwc] at hrd
  let e := firstState d
  have he := prepareFirst_exec (w := w) d
  have hre : Stack.Rep w base capacity (childWords x 1 ++ (childWords x 2 ++ vs))
      (e.comap registers) := by
    simpa only [e, firstState_comap] using hrd
  obtain ⟨z, hz, hrz, hfz, _⟩ := pushFrame_exec e (childWords x 1 ++ (childWords x 2 ++ vs))
    h2 hcap hre
    (fun i => (he.bounded (hd.bounded (hc.bounded (hb.bounded (ha.bounded hx))))).1 (slot i))
    (by simp only [List.length_append, length_childWords]; omega)
  have hwe : words e = childWords x 0 := by
    simp +decide [words, e, firstState, hpd, Outside, c, secondState, hpb, a, thirdState,
      childWords, Data.set, slot, original, heavyBase, heavyLength]
  change Stack.Rep w base capacity (words e ++ (childWords x 1 ++ (childWords x 2 ++ vs)))
    (z.comap registers) at hrz
  rw [hwe] at hrz
  have hrun : Exec w pushChildren x z 207 := ha.seq (hb.seq (hc.seq (hd.seq (he.seq hz))))
  refine ⟨z, hrun, ?_, ?_, fun i hi => hrun.regs_eq (pushChildren_preserves i hi)⟩
  · simpa only [List.append_assoc] using hrz
  · intro p hp
    exact (hfz p hp).trans ((hfd p hp).trans (hfb p hp))

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
