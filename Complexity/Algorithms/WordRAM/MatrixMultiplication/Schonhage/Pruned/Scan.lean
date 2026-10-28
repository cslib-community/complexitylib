/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ScanInsert

/-!
# Complete charged native query scans

## Main results

* `PrunedQuery.exec_scan`: the fixed native loop reads, filters and deduplicates its source
  list in at most `20 N + 5` instructions, without clearing a dense directory.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers changed by the whole scan, including its fresh-epoch initialization. -/
def ScanLocal (i : Fin registers) : Prop := ScanStepLocal i ∨ i = epoch

instance (i : Fin registers) : Decidable (ScanLocal i) :=
  inferInstanceAs (Decidable (ScanStepLocal i ∨ i = epoch))

private theorem scan_preserves (child : Bool) (i : Fin registers) :
    ¬ScanLocal i → (scan child).Preserves i := by decide +kernel +revert

/-- The actual native scan constructs a distinct query list and its membership timestamps.
All width premises concern ordinary addresses, lengths and the incoming epoch. Source/output/
directory separation is checked on concrete intervals. No child list is supplied in advance. -/
theorem exec_scan {w N capacity : ℕ} (child : Bool) (x : Data registers) (input : ℕ → ℕ)
    (hN : x.regs count = N)
    (hinput : ∀ i < N, x.mem (x.regs listBase + i) = input i)
    (hcodes : ∀ i < N, shortened child (input i) < capacity)
    (hsep : x.regs childList + capacity ≤ x.regs stamps ∨
      x.regs stamps + capacity ≤ x.regs childList)
    (hsrcOut : x.regs listBase + N ≤ x.regs childList ∨
      x.regs childList + capacity ≤ x.regs listBase)
    (hsrcStamp : x.regs listBase + N ≤ x.regs stamps ∨
      x.regs stamps + capacity ≤ x.regs listBase)
    (hmarks : ∀ q < capacity, x.mem (x.regs stamps + q) ≤ x.regs epoch)
    (h1 : x.regs one = 1) (h10 : x.regs ten = 10) (h9 : x.regs nine = 9)
    (hwidth : Fits w (x.regs listBase + N + x.regs childList + capacity +
      x.regs stamps + capacity + N + capacity + x.regs epoch + 12)) :
    ∃ y, ExecWithin w (scan child) x y (20 * N + 5) ∧ y.regs index = N ∧
      y.regs epoch = x.regs epoch + 1 ∧
      y.regs childCount = (scanSet child (x.regs term) input N).card ∧
      ScanMemory y.mem (x.regs childList) (x.regs stamps) (x.regs epoch + 1) capacity
        (scanSet child (x.regs term) input N) ∧
      (∀ i < N, y.mem (x.regs listBase + i) = input i) ∧
      (∀ a, ¬(Block.mk (x.regs childList) capacity).Owns a →
        ¬(Block.mk (x.regs stamps) capacity).Owns a → y.mem a = x.mem a) ∧
      (∀ i, ¬ScanLocal i → y.regs i = x.regs i) := by
  let E := x.regs epoch + 1
  let x0 := ((x.set epoch E).set childCount 0).set index 0
  have h0 : Fits w 0 := fits_zero w
  have hE : Fits w E := hwidth.of_le (by dsimp [E]; omega)
  have hsetup : ExecWithin w scanSetup x x0 3 := by
    ram_eval [scanSetup, x0, E, h1, hE, h0]
  let I (y : Data registers) : Prop :=
    y.regs index ≤ N ∧
    y.regs childCount = (scanSet child (x.regs term) input (y.regs index)).card ∧
    ScanMemory y.mem (x.regs childList) (x.regs stamps) E capacity
      (scanSet child (x.regs term) input (y.regs index)) ∧
    (∀ i < N, y.mem (x.regs listBase + i) = input i) ∧
    (∀ a, ¬(Block.mk (x.regs childList) capacity).Owns a →
      ¬(Block.mk (x.regs stamps) capacity).Owns a → y.mem a = x.mem a) ∧
    (∀ i, ¬ScanStepLocal i → y.regs i = x0.regs i)
  have hinit : I x0 := by
    refine ⟨by simp [x0], by simp +decide [x0, childCount, index], ?_, hinput, ?_,
      fun _ _ => rfl⟩
    · simpa only [x0, Data.set_mem, Data.set_regs, Function.update_self, scanSet_zero] using
        (ScanMemory.empty (out := x.regs childList) (epoch := E)
          (fun q hq => Nat.lt_succ_of_le (hmarks q hq)))
    · exact fun _ _ _ => rfl
  have hstep (y : Data registers) (hy : I y) (hc : (Cond.lt index count).Holds y) :
      ∃ z, ExecWithin w (scanStep child) y z 18 ∧ I z ∧
        N - z.regs index < N - y.regs index := by
    obtain ⟨hle, hcount, htable, hread, hframe, hfrozen⟩ := hy
    have hfixed (i : Fin registers) (hi : ¬ScanStepLocal i) (he : i ≠ epoch) :
        y.regs i = x.regs i := by
      rw [hfrozen i hi]
      simp only [x0, Data.set_regs]
      have hic : i ≠ childCount := by intro h; subst h; exact hi (by decide)
      have hii : i ≠ index := by intro h; subst h; exact hi (by decide)
      simp only [Function.update_of_ne hii, Function.update_of_ne hic,
        Function.update_of_ne he]
    have hye : y.regs epoch = E := by
      simpa +decide [x0, epoch, childCount, index] using hfrozen epoch (by decide)
    have hyb := hfixed listBase (by decide) (by decide)
    have hyo := hfixed childList (by decide) (by decide)
    have hys := hfixed stamps (by decide) (by decide)
    have hyt := hfixed term (by decide) (by decide)
    have hyn := (hfixed count (by decide) (by decide)).trans hN
    have hy1 := (hfixed one (by decide) (by decide)).trans h1
    have hy10 := (hfixed ten (by decide) (by decide)).trans h10
    have hy9 := (hfixed nine (by decide) (by decide)).trans h9
    have hk : y.regs index < N := by simpa only [Cond.holds_lt, hyn] using hc
    have hq := hcodes (y.regs index) hk
    have hcap := htable.card_le
    have hw10 : Fits w 10 := hwidth.of_le (by omega)
    have hwread : Fits w (y.regs listBase + y.regs index) :=
      hwidth.of_le (by rw [hyb]; omega)
    have hwstamp : Fits w (y.regs stamps + shortened child (input (y.regs index))) :=
      hwidth.of_le (by rw [hys]; omega)
    have hwout : Fits w (y.regs childList + y.regs childCount) :=
      hwidth.of_le (by rw [hyo, hcount]; omega)
    have hwcount : Fits w (y.regs childCount + 1) :=
      hwidth.of_le (by rw [hcount]; omega)
    have hwindex : Fits w (y.regs index + 1) := hwidth.of_le (by omega)
    obtain ⟨z, hz, hidx, hcz, htz, hmf, hrf⟩ := exec_scanInsert child y
      (scanSet child (x.regs term) input (y.regs index)) (input (y.regs index))
      (by rw [hyb]; exact hread _ hk) hcount
      (by simpa only [hyo, hys, hye] using htable) hq
      (by simpa only [hyo, hys] using hsep) hy1 hy10 hy9
      hw10 hwread hwstamp hwout hwcount hwindex
    have hsource (i : ℕ) (hi : i < N) : z.mem (x.regs listBase + i) = input i := by
      rw [hmf]
      · exact hread i hi
      · rw [hyo]
        change ¬(x.regs childList ≤ x.regs listBase + i ∧
          x.regs listBase + i < x.regs childList + capacity)
        rcases hsrcOut with h | h <;> omega
      · rw [hys]
        change ¬(x.regs stamps ≤ x.regs listBase + i ∧
          x.regs listBase + i < x.regs stamps + capacity)
        rcases hsrcStamp with h | h <;> omega
    refine ⟨z, hz, ?_, by omega⟩
    refine ⟨by omega, ?_, ?_, hsource, ?_, ?_⟩
    · simpa only [hyt, hidx, ← scanSet_succ] using hcz
    · simpa only [hyo, hys, hye, hyt, hidx, ← scanSet_succ] using htz
    · intro a hao has
      rw [hmf a (by simpa only [hyo] using hao) (by simpa only [hys] using has)]
      exact hframe a hao has
    · exact fun i hi => (hrf i hi).trans (hfrozen i hi)
  obtain ⟨y, hy, hIy, hstop⟩ := ExecWithin.loop_invariant I (fun y => N - y.regs index)
    hstep hinit
  obtain ⟨hle, hcount, htable, hread, hframe, hfrozen⟩ := hIy
  have hyn : y.regs count = N := by
    have := hfrozen count (by decide)
    simpa +decide [x0, count, epoch, childCount, index] using this.trans (by
      simpa +decide [x0, count, epoch, childCount, index] using hN)
  have hindex : y.regs index = N := by
    simp only [Cond.holds_lt, hyn, not_lt] at hstop
    omega
  have he : ExecWithin w (scan child) x y (20 * N + 5) := by
    have hloop : ExecWithin w (Code.loop (.lt index count) (scanStep child)) x0 y
        (20 * N + 2) := by
      simpa only [x0, Data.set_regs, Function.update_self, Nat.sub_zero,
        Nat.mul_comm] using hy
    exact (hsetup.seq hloop).mono (by omega)
  refine ⟨y, he, hindex, ?_, ?_, ?_, hread, hframe,
    fun i hi => he.regs_eq (scan_preserves child i hi)⟩
  · simpa +decide [x0, E, epoch, childCount, index] using hfrozen epoch (by decide)
  · simpa only [hindex] using hcount
  · simpa only [hindex] using htable

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
