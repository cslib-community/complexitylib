/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory

/-!
# Sparse initialization of requested accumulators

## Main definitions

* `PrunedQuery.zeroQueryPrefix`: the memory after zeroing a listed prefix of query addresses.

## Main results

* `PrunedQuery.exec_clearRequested`: actual indexed clearing within `7 N + 3` instructions.

Repeated requests are permitted. Unlisted cells are preserved, and no dense value directory
is initialized by this routine.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Finset

/-- Clear precisely the addresses named in the processed prefix of an explicit query list. -/
def zeroQueryPrefix (mem : ℕ → ℕ) (base : ℕ) (input : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  fun a => if a ∈ (range k).image (fun i => base + input i) then 0 else mem a

/-- Clearing no requests leaves memory unchanged. -/
@[simp]
theorem zeroQueryPrefix_zero (mem : ℕ → ℕ) (base : ℕ) (input : ℕ → ℕ) :
    zeroQueryPrefix mem base input 0 = mem := by ext a; simp [zeroQueryPrefix]

/-- One additional listed request is exactly one memory store, including repeated requests. -/
theorem zeroQueryPrefix_succ (mem : ℕ → ℕ) (base : ℕ) (input : ℕ → ℕ) (k : ℕ) :
    zeroQueryPrefix mem base input (k + 1) =
      Function.update (zeroQueryPrefix mem base input k) (base + input k) 0 := by
  ext a
  by_cases ha : a = base + input k <;>
    simp [zeroQueryPrefix, range_add_one, image_insert, ha]

/-- Every cell outside the concrete value directory is preserved by a bounded prefix. -/
theorem zeroQueryPrefix_outside {mem : ℕ → ℕ} {base capacity k : ℕ} {input : ℕ → ℕ}
    (hcode : ∀ i < k, input i < capacity) {a : ℕ}
    (ha : ¬(Block.mk base capacity).Owns a) : zeroQueryPrefix mem base input k a = mem a := by
  have hnot : a ∉ (range k).image (fun i => base + input i) := by
    rintro h
    obtain ⟨i, hi, rfl⟩ := mem_image.mp h
    apply ha
    change base ≤ base + input i ∧ base + input i < base + capacity
    have := hcode i (mem_range.mp hi)
    omega
  simp only [zeroQueryPrefix, hnot, ↓reduceIte]

/-- Registers modified by sparse clearing. -/
def ClearLocal (i : Fin registers) : Prop := i = address ∨ i = query ∨ i = index

instance (i : Fin registers) : Decidable (ClearLocal i) :=
  inferInstanceAs (Decidable (i = address ∨ i = query ∨ i = index))

private theorem clearStep_preserves (i : Fin registers) :
    ¬ClearLocal i → clearValueStep.Preserves i := by decide +kernel +revert

private theorem clear_preserves (i : Fin registers) :
    ¬ClearLocal i → clearRequested.Preserves i := by decide +kernel +revert

/-- Each requested word costs an indexed source load, indexed zero store and increment. -/
theorem exec_clearValueStep {w : ℕ} (x : Data registers) (q : ℕ)
    (hq : x.mem (x.regs listBase + x.regs index) = q)
    (h0 : x.regs nil = 0) (h1 : x.regs one = 1)
    (hr : Fits w (x.regs listBase + x.regs index))
    (hv : Fits w (x.regs valueBase + q)) (hi : Fits w (x.regs index + 1)) :
    ∃ y, ExecWithin w clearValueStep x y 5 ∧ y.regs index = x.regs index + 1 ∧
      y.mem = Function.update x.mem (x.regs valueBase + q) 0 ∧
      (∀ i, ¬ClearLocal i → y.regs i = x.regs i) := by
  let y := (((((x.set address (x.regs listBase + x.regs index)).set query q).set
    address (x.regs valueBase + q)).write (x.regs valueBase + q) 0).set
    index (x.regs index + 1))
  have he : ExecWithin w clearValueStep x y 5 := by
    ram_eval [clearValueStep, y, hq, h0, h1, hr, hv, hi, address, query, index, listBase,
      valueBase, nil, one, Fin.mk.injEq]
  exact ⟨y, he, by simp [y], rfl, fun i hi => he.regs_eq (clearStep_preserves i hi)⟩

/-- The fixed native clearing loop visits only explicit requests. Width follows from concrete
source/destination endpoints and lengths, and source preservation follows from their separation. -/
theorem exec_clearRequested {w N capacity : ℕ} (x : Data registers) (input : ℕ → ℕ)
    (hN : x.regs count = N)
    (hinput : ∀ i < N, x.mem (x.regs listBase + i) = input i)
    (hcode : ∀ i < N, input i < capacity)
    (hsep : x.regs listBase + N ≤ x.regs valueBase ∨
      x.regs valueBase + capacity ≤ x.regs listBase)
    (h0 : x.regs nil = 0) (h1 : x.regs one = 1)
    (hw : Fits w (x.regs listBase + N + x.regs valueBase + capacity + N + 2)) :
    ∃ y, ExecWithin w clearRequested x y (7 * N + 3) ∧ y.regs index = N ∧
      y.mem = zeroQueryPrefix x.mem (x.regs valueBase) input N ∧
      (∀ i < N, y.mem (x.regs listBase + i) = input i) ∧
      (∀ i, ¬ClearLocal i → y.regs i = x.regs i) := by
  let x0 := x.set index 0
  let I (y : Data registers) : Prop := y.regs index ≤ N ∧
    y.mem = zeroQueryPrefix x.mem (x.regs valueBase) input (y.regs index) ∧
    (∀ i, ¬ClearLocal i → y.regs i = x.regs i)
  have hinit : I x0 := by
    refine ⟨by simp [x0], by simp [x0], ?_⟩
    intro i hi
    have hne : i ≠ index := by intro h; subst h; exact hi (Or.inr (Or.inr rfl))
    simp [x0, hne]
  have hread (y : Data registers) (hy : I y) (i : ℕ) (hi : i < N) :
      y.mem (x.regs listBase + i) = input i := by
    rw [hy.2.1, zeroQueryPrefix_outside (fun j hj => hcode j (by omega))]
    · exact hinput i hi
    · change ¬(x.regs valueBase ≤ x.regs listBase + i ∧
        x.regs listBase + i < x.regs valueBase + capacity)
      rcases hsep with h | h <;> omega
  have hstep (y : Data registers) (hy : I y) (hc : (Cond.lt index count).Holds y) :
      ∃ z, ExecWithin w clearValueStep y z 5 ∧ I z ∧
        N - z.regs index < N - y.regs index := by
    obtain ⟨hle, hm, hf⟩ := hy
    have hcount := (hf count (by decide)).trans hN
    have hb := hf listBase (by decide)
    have hv := hf valueBase (by decide)
    have hnil := (hf nil (by decide)).trans h0
    have hone := (hf one (by decide)).trans h1
    have hk : y.regs index < N := by simpa only [Cond.holds_lt, hcount] using hc
    have hq := hcode (y.regs index) hk
    obtain ⟨z, hz, hi, hmem, hregs⟩ := exec_clearValueStep y (input (y.regs index))
      (by rw [hb]; exact hread y ⟨hle, hm, hf⟩ _ hk) hnil hone
      (hw.of_le (by rw [hb]; omega)) (hw.of_le (by rw [hv]; omega)) (hw.of_le (by omega))
    refine ⟨z, hz, ⟨by omega, ?_, fun i hi => (hregs i hi).trans (hf i hi)⟩, by omega⟩
    rw [hmem, hm, hv, hi, zeroQueryPrefix_succ]
  obtain ⟨y, hy, hIy, hstop⟩ := ExecWithin.loop_invariant I (fun y => N - y.regs index)
    hstep hinit
  have hcount := (hIy.2.2 count (by decide)).trans hN
  have hindex : y.regs index = N := by
    simp only [Cond.holds_lt, hcount, not_lt] at hstop
    omega
  have hsetup : ExecWithin w (ram[ index ← #0 ] : Code .standard registers) x x0 1 := by
    ram_eval [x0]
  have hloop : ExecWithin w (Code.loop (.lt index count) clearValueStep) x0 y (7 * N + 2) := by
    simpa only [x0, Data.set_regs, Function.update_self, Nat.sub_zero, Nat.mul_comm] using hy
  have he : ExecWithin w clearRequested x y (7 * N + 3) :=
    (hsetup.seq hloop).mono (by omega)
  refine ⟨y, he, hindex, ?_, hread y hIy, fun i hi => he.regs_eq (clear_preserves i hi)⟩
  simpa only [hindex] using hIy.2.1

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
