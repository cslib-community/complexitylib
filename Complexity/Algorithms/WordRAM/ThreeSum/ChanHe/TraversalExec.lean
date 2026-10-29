/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalProgram

/-!
# Charged native execution of the Chan–He traversal controller

The zero-fuel case executes setup, a complete record push, a complete record pop, both loop
tests, and the skip branch. It preserves the accumulated output count, heap and memory outside
the reserved stack. It does not silently replace a negative 3SUM instance by an empty output.

## Main results

* `oneRoot_zero`: exact 173-instruction execution of the complete controller at zero fuel.

The controller composition proofs are original. General supplied-root traversal correctness is
proved in `TraversalRoot.root_exec`; complete initialized-input preprocessing is composed in
`PreprocessingInput.runs_input`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- Even zero fuel executes all native setup and stack work. No node is emitted, and the root
record is recovered exactly. Existing output arrays and all non-stack memory are preserved. -/
theorem oneRoot_zero {w capacity : ℕ} (x : Data 128) (hx : x.Bounded w)
    (h2 : Fits w 2) (hcap : Fits w (x.regs stackBase + capacity))
    (hcapacity : 7 ≤ capacity) (hf : x.regs (slot 0) = 0) :
    ∃ y, Exec w oneRoot x y 173 ∧
      Stack.Rep w (x.regs stackBase) capacity [] (y.comap registers) ∧
      (∀ i, y.regs (slot i) = x.regs (slot i)) ∧
      y.regs outputCount = x.regs outputCount ∧ y.regs heap = x.regs heap ∧
      Modifies (Stack.footprint (x.regs stackBase) capacity) x.mem y.mem := by
  let a := (((x.set zero 0).set one 1).set (registers Stack.ptr) (x.regs stackBase)).set
    (registers Stack.len) 0
  have h1 : Fits w 1 := h2.of_le (by decide)
  have ha : Exec (B := .standard) w
      (.seq (.op (.const zero 0)) (.seq (.op (.const one 1))
        (.seq (.op (.copy (registers Stack.ptr) stackBase))
          (.op (.const (registers Stack.len) 0))))) x a 4 := by
    ram_eval [a, zero, one, registers, Stack.ptr, Stack.len, stackBase, h1]
  have haslots (i : Fin 7) : a.regs (slot i) = x.regs (slot i) := by
    fin_cases i <;> simp +decide [a, slot, registers, Stack.ptr, Stack.len, zero, one]
  have har : Stack.Rep w (x.regs stackBase) capacity [] (a.comap registers) := by
    refine ⟨⟨fun i => (ha.bounded hx).1 (registers i), (ha.bounded hx).2⟩,
      ?_, ?_, Nat.zero_le _, fun i => Fin.elim0 i⟩
    · simp +decide [a, registers, Stack.ptr, Stack.len, zero, one]
    · simp +decide [a, registers, Stack.ptr, Stack.len, zero, one]
  obtain ⟨b, hb, hrb, hfb, hpb⟩ := pushFrame_exec a [] h2 hcap har
    (fun i => (ha.bounded hx).1 (slot i)) (by simpa using hcapacity)
  obtain ⟨c, hc, hrc, hcs, hfc, hpc⟩ := popFrame_exec b [] (fun i => a.regs (slot i)) h2 hcap hrb
  have hbzero : b.regs zero = 0 := by
    rw [hpb zero (Or.inl (by decide))]
    simp +decide [a, registers, Stack.ptr, Stack.len, zero, one]
  have hczero : c.regs zero = 0 := by
    rw [hpc zero (Or.inl (by decide)) (by decide), hbzero]
  have hcf : c.regs (slot 0) = 0 := (hcs 0).trans ((haslots 0).trans hf)
  have hblen : b.regs (registers Stack.len) = 7 := by
    simpa only [Data.comap_regs, List.length_append, List.length_cons, List.length_nil,
      Nat.reduceAdd] using hrb.length_eq
  have hclen : c.regs (registers Stack.len) = 0 := hrc.length_eq
  have hcopy : Exec (B := .standard) w (.op (.copy (slot 0) (slot 0))) c c 1 := by
    convert (Exec.copy (B := Basis.standard) (w := w) (x := c)
      (d := slot 0) (s := slot 0)) using 1
    ext i <;> simp [Data.set]
  have hbody : Exec w body b c 101 := by
    exact hc.seq (Exec.branch_pos (by change c.regs (slot 0) = c.regs zero; omega) hcopy)
  have hl : Exec w loop b c 105 := by
    apply Exec.loop_once
    · change b.regs zero < b.regs (registers Stack.len)
      omega
    · exact hbody
    · change ¬c.regs zero < c.regs (registers Stack.len)
      omega
  refine ⟨c, ha.seq (hb.seq hl), hrc, fun i => (hcs i).trans (haslots i), ?_, ?_, ?_⟩
  · rw [hpc outputCount (Or.inl (by decide)) (by decide),
      hpb outputCount (Or.inl (by decide))]
    simp +decide [a, registers, Stack.ptr, Stack.len, outputCount, zero, one]
  · rw [hpc heap (Or.inl (by decide)) (by decide), hpb heap (Or.inl (by decide))]
    simp +decide [a, registers, Stack.ptr, Stack.len, heap, zero, one]
  · intro p hp
    exact (hfc p hp).trans (hfb p hp)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
