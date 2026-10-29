/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Scan
public import Complexity.Computability.WordRAM.Heap

/-!
# Initialization of the actual root stack frame

## Main results

* `PrunedQuery.exec_rootFinish`: write the computed root count and enter its first phase.

The count comes from the preceding native deduplication. The frame words are ordinary stores,
not an externally supplied traversal certificate.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers assigned after the actual root query list has been computed. -/
def RootFinishLocal (i : Fin registers) : Prop :=
  i = address ∨ i = level ∨ i = mode ∨ i = active

instance (i : Fin registers) : Decidable (RootFinishLocal i) :=
  inferInstanceAs (Decidable (i = address ∨ i = level ∨ i = mode ∨ i = active))

private theorem rootFinish_preserves (i : Fin registers) :
    ¬RootFinishLocal i → rootFinish.Preserves i := by decide +kernel +revert

/-- Eleven native instructions write the root's computed count, zero prefix, unit stride and
zero term, then set the controller to its entry phase. -/
theorem exec_rootFinish {w : ℕ} (x : Data registers) (h0 : x.regs nil = 0)
    (h1 : x.regs one = 1) (hw : Fits w (x.regs frames + 3)) :
    ∃ y, ExecWithin w rootFinish x y 11 ∧ y.regs level = 0 ∧ y.regs mode = 0 ∧
      y.regs active = 1 ∧
      y.mem = Function.update (Function.update (Function.update (Function.update x.mem
        (x.regs frames) (x.regs childCount)) (x.regs frames + 1) 0)
        (x.regs frames + 2) 1) (x.regs frames + 3) 0 ∧
      Modifies (Block.mk (x.regs frames) 4).footprint x.mem y.mem ∧
      (∀ i, ¬RootFinishLocal i → y.regs i = x.regs i) := by
  let f := x.regs frames
  let y := (((((((((((x.set address f).write f (x.regs childCount)).set address (f + 1)).write
    (f + 1) 0).set address (f + 2)).write (f + 2) 1).set address (f + 3)).write
    (f + 3) 0).set level 0).set mode 0).set active 1)
  have hconst : Fits w 1 := hw.of_le (by omega)
  have hf1 : Fits w (x.regs frames + 1) := hw.of_le (by omega)
  have hf2 : Fits w (x.regs frames + 2) := hw.of_le (by omega)
  have he : ExecWithin w rootFinish x y 11 := by
    ram_eval [rootFinish, y, f, h0, h1, hw, hconst, hf1, hf2, address, level, mode, active,
      one, nil, childCount, frames, Fin.mk.injEq]
  refine ⟨y, he, ?_, ?_, by simp [y], rfl, ?_,
    fun i hi => he.regs_eq (rootFinish_preserves i hi)⟩
  · simp +decide [y, active, mode, level]
  · simp +decide [y, active, mode]
  · intro a ha
    have hnot : ¬(f ≤ a ∧ a < f + 4) := by
      simpa only [Block.mem_footprint, Block.Owns, f, Block.base, Block.length] using ha
    have h0' : a ≠ f := by omega
    have h1' : a ≠ f + 1 := by omega
    have h2' : a ≠ f + 2 := by omega
    have h3' : a ≠ f + 3 := by omega
    simp only [y, Data.set_mem, Data.write_mem, Function.update_of_ne h3',
      Function.update_of_ne h2', Function.update_of_ne h1', Function.update_of_ne h0']

/-- Registers written by root-list construction and its first frame initialization. -/
def RootLocal (i : Fin registers) : Prop :=
  ScanLocal i ∨ RootFinishLocal i ∨ i = listBase ∨ i = count ∨ i = childList

instance (i : Fin registers) : Decidable (RootLocal i) :=
  inferInstanceAs (Decidable
    (ScanLocal i ∨ RootFinishLocal i ∨ i = listBase ∨ i = count ∨ i = childList))

private theorem rootList_preserves (i : Fin registers) :
    ¬RootLocal i → rootList.Preserves i := by decide +kernel +revert

/-- Construct the actual distinct root list and frame. Repeated input queries are read and
removed by the native timestamp scan, rather than supplied as a mathematical set. The frame,
list and timestamp intervals are the only possible memory writes. -/
theorem exec_rootList {w N capacity : ℕ} (x : Data registers) (input : ℕ → ℕ)
    (hN : x.regs queryCount = N)
    (hinput : ∀ i < N, x.mem (x.regs queries + i) = input i)
    (hcodes : ∀ i < N, input i < capacity)
    (hsep : x.regs lists + capacity ≤ x.regs stamps)
    (hsrcOut : x.regs queries + N ≤ x.regs lists)
    (hframeList : x.regs frames + 4 ≤ x.regs lists)
    (hsrcFrame : x.regs queries + N ≤ x.regs frames)
    (hmarks : ∀ q < capacity, x.mem (x.regs stamps + q) ≤ x.regs epoch)
    (h0 : x.regs nil = 0) (h1 : x.regs one = 1)
    (h10 : x.regs ten = 10) (h9 : x.regs nine = 9)
    (hw : Fits w (x.regs queries + N + x.regs lists + capacity +
      x.regs stamps + capacity + N + capacity + x.regs epoch + x.regs frames + 16)) :
    ∃ y, ExecWithin w rootList x y (20 * N + 19) ∧
      y.regs level = 0 ∧ y.regs mode = 0 ∧ y.regs active = 1 ∧
      y.regs epoch = x.regs epoch + 1 ∧
      ScanMemory y.mem (x.regs lists) (x.regs stamps) (x.regs epoch + 1) capacity
        ((Finset.range N).image input) ∧
      y.mem (x.regs frames) = ((Finset.range N).image input).card ∧
      y.mem (x.regs frames + 1) = 0 ∧ y.mem (x.regs frames + 2) = 1 ∧
      y.mem (x.regs frames + 3) = 0 ∧
      (∀ i < N, y.mem (x.regs queries + i) = input i) ∧
      (∀ a, ¬(Block.mk (x.regs lists) capacity).Owns a →
        ¬(Block.mk (x.regs stamps) capacity).Owns a →
        ¬(Block.mk (x.regs frames) 4).Owns a → y.mem a = x.mem a) ∧
      (∀ i, ¬RootLocal i → y.regs i = x.regs i) := by
  let u := ((x.set listBase (x.regs queries)).set count N).set childList (x.regs lists)
  have hu : ExecWithin w rootScanSetup x u 3 := by
    ram_eval [rootScanSetup, u, hN, listBase, count, childList, queryCount, queries, lists,
      Fin.mk.injEq]
  obtain ⟨v, hv, _, hve, hvc, htable, _, hscanFrame, hvreg⟩ := exec_scan (N := N)
    (capacity := capacity) false u input
    (by simp +decide [u, count, childList])
    (by simpa +decide [u, listBase, count, childList] using hinput)
    (by simpa only [shortened, Bool.false_eq_true, ↓reduceIte] using hcodes)
    (Or.inl (by simpa +decide [u, childList, stamps, count, listBase] using hsep))
    (Or.inl (by simpa +decide [u, childList, listBase, count] using hsrcOut))
    (Or.inl (by simpa +decide [u, stamps, listBase, count, childList] using
      hsrcOut.trans (Nat.le_trans (Nat.le_add_right _ _) hsep)))
    (by simpa +decide [u, stamps, epoch, childList, count, listBase] using hmarks)
    (by simpa +decide [u, one, childList, count, listBase] using h1)
    (by simpa +decide [u, ten, childList, count, listBase] using h10)
    (by simpa +decide [u, nine, childList, count, listBase] using h9)
    (hw.of_le (by simp +decide [u, listBase, count, childList, stamps, epoch]; omega))
  have fixed (i : Fin registers) (hi : ¬ScanLocal i)
      (hb : i ≠ listBase) (hc : i ≠ count) (ho : i ≠ childList) :
      v.regs i = x.regs i := by
    rw [hvreg i hi]
    simp only [u, Data.set_regs, Function.update_of_ne ho, Function.update_of_ne hc,
      Function.update_of_ne hb]
  have hvf := fixed frames (by decide) (by decide) (by decide) (by decide)
  have hvs := fixed stamps (by decide) (by decide) (by decide) (by decide)
  obtain ⟨y, hy, hyl, hym, hya, hmem, hfinishFrame, _⟩ := exec_rootFinish v
    ((fixed nil (by decide) (by decide) (by decide) (by decide)).trans h0)
    ((fixed one (by decide) (by decide) (by decide) (by decide)).trans h1)
    (hw.of_le (by rw [hvf]; omega))
  have he : ExecWithin w rootList x y (20 * N + 19) := by
    exact (hu.seq (hv.seq hy)).mono (by omega)
  have hyoutside (a : ℕ) (ha : ¬(Block.mk (x.regs frames) 4).Owns a) :
      y.mem a = v.mem a := hfinishFrame a (by simpa only [Block.mem_footprint, hvf] using ha)
  have hawayList (i : ℕ) : ¬(Block.mk (x.regs frames) 4).Owns (x.regs lists + i) := by
    change ¬(x.regs frames ≤ _ ∧ _ < x.regs frames + 4)
    omega
  have hawayStamp (i : ℕ) : ¬(Block.mk (x.regs frames) 4).Owns (x.regs stamps + i) := by
    change ¬(x.regs frames ≤ _ ∧ _ < x.regs frames + 4)
    omega
  have htable' : ScanMemory v.mem (x.regs lists) (x.regs stamps) (x.regs epoch + 1)
      capacity ((Finset.range N).image input) := by
    simpa +decide [u, childList, stamps, epoch, listBase, count, term, scanSet_root] using htable
  refine ⟨y, he, hyl, hym, hya, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => he.regs_eq (rootList_preserves i hi)⟩
  · simpa +decide [hy.regs_eq (by decide : rootFinish.Preserves epoch), u, epoch,
      childList, count, listBase] using hve
  · exact htable'.congr (fun i _ => hyoutside _ (hawayList i))
      (fun q _ => hyoutside _ (hawayStamp q))
  · rw [hmem, hvf]
    simpa +decide [Function.update_apply, u, childList, count, listBase, term, scanSet_root]
      using hvc
  · rw [hmem, hvf]
    simp
  · rw [hmem, hvf]
    simp
  · rw [hmem, hvf]
    simp
  · intro i hi
    rw [hyoutside _ (by change ¬(x.regs frames ≤ _ ∧ _ < x.regs frames + 4); omega)]
    rw [hscanFrame]
    · exact hinput i hi
    · change ¬(u.regs childList ≤ _ ∧ _ < u.regs childList + capacity)
      simp +decide only [u, Data.set_regs, childList, count, listBase,
        Function.update_apply, ↓reduceIte]
      omega
    · change ¬(u.regs stamps ≤ _ ∧ _ < u.regs stamps + capacity)
      have hus : u.regs stamps = x.regs stamps := by
        simp +decide [u, stamps, childList, count, listBase]
      rw [hus]
      omega
  · intro a hao has haf
    rw [hyoutside a haf, hscanFrame]
    · rfl
    · simpa +decide [u, childList, count, listBase] using hao
    · simpa +decide [u, stamps, childList, count, listBase] using has

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
