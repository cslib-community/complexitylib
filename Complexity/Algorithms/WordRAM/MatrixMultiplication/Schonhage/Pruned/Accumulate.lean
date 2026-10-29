/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.AccumulateStep
public import Complexity.Computability.WordRAM.Heap

/-!
# Complete native accumulation over a distinct parent list

## Main results

* `PrunedQuery.exec_accumulateLoop`: the native loop adds a returned child exactly once at
  each contributing listed parent query, within `31 N + 3` instructions.

The loop invariant uses Mathlib's existing `Finset.piecewise` for the updated memory cells.
The source list and child values are preserved by the concrete block separations.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed Finset

private theorem accumulateLoop_preserves (i : Fin registers) :
    ¬AccumulateStepLocal i → accumulateLoop.Preserves i := by decide +kernel +revert

/-- This is the real indexed signed-add loop. The list's distinctness is its ordinary memory
property, established by the preceding native timestamp scan, not a query-decision oracle. -/
theorem exec_accumulateLoop {w N capacity : ℕ} (x : Data registers) (input : ℕ → ℕ)
    (V B : ℕ → ℤ) (hN : x.regs count = N)
    (hinput : ∀ i < N, x.mem (x.regs listBase + i) = input i)
    (hcode : ∀ i < N, input i < capacity)
    (hinj : Set.InjOn input {i | i < N})
    (hparent : ∀ i < N, x.mem (x.regs valueBase + input i) = encode (V (input i)))
    (hchild : ∀ i < N, selected true (x.regs term) (input i) →
      x.mem (x.regs childValues + input i / 10) = encode (B (input i / 10)))
    (hV : ∀ i < N, GenericRAM.Signed.Fits w (V (input i)))
    (hB : ∀ i < N, GenericRAM.Signed.Fits w (B (input i / 10)))
    (hsepSource : x.regs listBase + N ≤ x.regs valueBase ∨
      x.regs valueBase + capacity ≤ x.regs listBase)
    (hsepChild : x.regs valueBase + capacity ≤ x.regs childValues ∨
      x.regs childValues + capacity ≤ x.regs valueBase)
    (h1 : x.regs one = 1) (h9 : x.regs nine = 9) (h10 : x.regs ten = 10)
    (hw : Fits (w + 2) (x.regs listBase + N + x.regs valueBase + capacity +
      x.regs childValues + capacity + N + 16)) :
    ∃ y, ExecWithin (w + 2) accumulateLoop x y (31 * N + 3) ∧ y.regs index = N ∧
      y.mem = (((range N).filter fun i => selected true (x.regs term) (input i)).image
        fun i => x.regs valueBase + input i).piecewise
          (fun a => encode (V (a - x.regs valueBase) + B ((a - x.regs valueBase) / 10))) x.mem ∧
      Modifies (Block.mk (x.regs valueBase) capacity).footprint x.mem y.mem ∧
      (∀ i < N, y.mem (x.regs listBase + i) = input i) ∧
      (∀ i, ¬AccumulateStepLocal i → y.regs i = x.regs i) := by
  let written (k : ℕ) := (((range k).filter fun i =>
    selected true (x.regs term) (input i)).image fun i => x.regs valueBase + input i)
  let newValue (a : ℕ) :=
    encode (V (a - x.regs valueBase) + B ((a - x.regs valueBase) / 10))
  let x0 := x.set index 0
  let I (y : Data registers) : Prop := y.regs index ≤ N ∧
    y.mem = (written (y.regs index)).piecewise newValue x.mem ∧
    (∀ i, ¬AccumulateStepLocal i → y.regs i = x.regs i)
  have hinit : I x0 := by
    refine ⟨by simp [x0], ?_, ?_⟩
    · funext a
      simp [x0, written, Finset.piecewise]
    · intro i hi
      have hne : i ≠ index := by intro h; subst h; exact hi (by decide)
      simp [x0, hne]
  have houtside (y : Data registers) (hy : I y) (a : ℕ)
      (ha : ¬(Block.mk (x.regs valueBase) capacity).Owns a) : y.mem a = x.mem a := by
    have hnot : a ∉ written (y.regs index) := by
      rintro h
      obtain ⟨i, hi, rfl⟩ := mem_image.mp h
      have hik := mem_range.mp (mem_filter.mp hi).1
      have hq := hcode i (lt_of_lt_of_le hik hy.1)
      apply ha
      change x.regs valueBase ≤ x.regs valueBase + input i ∧
        x.regs valueBase + input i < x.regs valueBase + capacity
      omega
    rw [hy.2.1]
    simp only [Finset.piecewise, hnot, ↓reduceIte]
  have hread (y : Data registers) (hy : I y) (i : ℕ) (hi : i < N) :
      y.mem (x.regs listBase + i) = input i := by
    rw [houtside y hy]
    · exact hinput i hi
    · change ¬(x.regs valueBase ≤ x.regs listBase + i ∧
        x.regs listBase + i < x.regs valueBase + capacity)
      rcases hsepSource with h | h <;> omega
  have hstep (y : Data registers) (hy : I y) (hc : (Cond.lt index count).Holds y) :
      ∃ z, ExecWithin (w + 2) accumulateStep y z 29 ∧ I z ∧
        N - z.regs index < N - y.regs index := by
    obtain ⟨hle, hmem, hf⟩ := hy
    have hcount := (hf count (by decide)).trans hN
    have hb := hf listBase (by decide)
    have hv := hf valueBase (by decide)
    have hcptr := hf childValues (by decide)
    have ht := hf term (by decide)
    have hk : y.regs index < N := by simpa only [Cond.holds_lt, hcount] using hc
    have hq := hcode (y.regs index) hk
    have hquot : input (y.regs index) / 10 < capacity :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hq
    have hnot : x.regs valueBase + input (y.regs index) ∉ written (y.regs index) := by
      rintro h
      obtain ⟨j, hj, he⟩ := mem_image.mp h
      have hjk := mem_range.mp (mem_filter.mp hj).1
      have hji := hinj (lt_of_lt_of_le hjk hle) hk (Nat.add_left_cancel he)
      omega
    have hleft : y.mem (y.regs valueBase + input (y.regs index)) =
        encode (V (input (y.regs index))) := by
      rw [hv, hmem]
      simp only [Finset.piecewise, hnot, ↓reduceIte]
      exact hparent _ hk
    have hright (hs : selected true (y.regs term) (input (y.regs index))) :
        y.mem (y.regs childValues + input (y.regs index) / 10) =
          encode (B (input (y.regs index) / 10)) := by
      rw [hcptr, houtside y ⟨hle, hmem, hf⟩]
      · exact hchild _ hk (by simpa only [ht] using hs)
      · change ¬(x.regs valueBase ≤ x.regs childValues + input (y.regs index) / 10 ∧
          x.regs childValues + input (y.regs index) / 10 < x.regs valueBase + capacity)
        rcases hsepChild with h | h <;> omega
    obtain ⟨z, hz, hi, hm, hregs⟩ := exec_accumulateStep (hV _ hk) (hB _ hk) y
      (input (y.regs index)) (by rw [hb]; exact hread y ⟨hle, hmem, hf⟩ _ hk)
      ((hf one (by decide)).trans h1) ((hf nine (by decide)).trans h9)
      ((hf ten (by decide)).trans h10) (fun _ => hleft) hright
      (hw.of_le (by omega)) (hw.of_le (by rw [hb]; omega))
      (hw.of_le (by rw [hv]; omega)) (hw.of_le (by rw [hcptr]; omega)) (hw.of_le (by omega))
    refine ⟨z, hz, ⟨by omega, ?_, fun i hi => (hregs i hi).trans (hf i hi)⟩, by omega⟩
    have hnext : written (y.regs index + 1) =
        if selected true (x.regs term) (input (y.regs index)) then
          insert (x.regs valueBase + input (y.regs index)) (written (y.regs index))
        else written (y.regs index) := by
      by_cases hs : selected true (x.regs term) (input (y.regs index)) <;>
        simp [written, range_add_one, filter_insert, hs]
    rw [hm, ht, hv, hmem, hi, hnext]
    funext a
    by_cases hs : selected true (x.regs term) (input (y.regs index))
    · by_cases he : a = x.regs valueBase + input (y.regs index)
      · subst a
        simp [hs, Finset.piecewise, newValue]
      · simp [hs, Finset.piecewise, he, newValue]
    · simp [hs, Finset.piecewise, newValue]
  obtain ⟨y, hy, hIy, hstop⟩ := ExecWithin.loop_invariant I (fun y => N - y.regs index)
    hstep hinit
  have hcount := (hIy.2.2 count (by decide)).trans hN
  have hindex : y.regs index = N := by
    simp only [Cond.holds_lt, hcount, not_lt] at hstop
    omega
  have hsetup : ExecWithin (w + 2) (ram[ index ← #0 ] : Code .standard registers) x x0 1 := by
    ram_eval [x0]
  have hloop : ExecWithin (w + 2) (Code.loop (.lt index count) accumulateStep) x0 y
      (31 * N + 2) := by
    simpa only [x0, Data.set_regs, Function.update_self, Nat.sub_zero, Nat.mul_comm] using hy
  have he : ExecWithin (w + 2) accumulateLoop x y (31 * N + 3) :=
    (hsetup.seq hloop).mono (by omega)
  refine ⟨y, he, hindex, ?_, ?_, hread y hIy,
    fun i hi => he.regs_eq (accumulateLoop_preserves i hi)⟩
  · change y.mem = (written N).piecewise newValue x.mem
    rw [← hindex]
    exact hIy.2.1
  · intro a ha
    exact houtside y hIy a (by simpa only [Block.mem_footprint] using ha)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
