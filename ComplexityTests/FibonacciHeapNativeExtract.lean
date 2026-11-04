/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Extract
public import ComplexityTests.FibonacciHeapNativeExtractSource
public import ComplexityTests.FibonacciHeapNativeCut
public import Complexity.Computability.WordRAM.Realization.Witness

/-!
# The same native Fibonacci extractor on actual source heaps

The original allocator supplies a zero-capacity three-bit heap and a maximum-key singleton.
An actual prior source extraction supplies a minimum with a child, exercising preparation,
scattering and gathering. Each test uses the same selected emitter and retains full memory,
frontier and the original unshifted three-word optional-pair encoding.
-/

public section

namespace ComplexityTests.FibonacciHeapNativeExtract

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap FibonacciHeap.Native
open FibonacciHeapNativeExtractSource FibonacciHeapNativeCut

private theorem zero_valid : extractValid 3 ![0, 2] emptyZero := by
  let a := zeroAllocator (n := 0) (K := 7) (w := 3) (by decide) (by decide)
  have hv : (indexedMinPQSpec 0 7).ValidHistory a.init
      ((indexedMinPQSpec 0 7).clientHistory a.init (pure ())) := trivial
  have hi : (framed (n := 0) (K := 7) (w := 3) (by decide) (by decide) 2).inv emptyZero :=
    (a.run_correct (pure ()) (Memory.zeroAbove_init [7]) (by decide) hv).2.2.1
  exact ⟨by decide, hi.1, 7, by decide, hi.2⟩

private theorem singleton_valid : extractValid 5 ![1, 2] singleton := by
  let a := zeroAllocator (n := 1) (K := 31) (w := 5) (by decide) (by decide)
  have hv : (indexedMinPQSpec 1 31).ValidHistory a.init
      ((indexedMinPQSpec 1 31).clientHistory a.init
        ((indexedMinPQSpec 1 31).call (.insert 0 31))) := by
    change ((none : Option ℕ) = none ∧ (31 : ℕ) ≤ 31) ∧ True
    decide
  have hi : (framed (n := 1) (K := 31) (w := 5) (by decide) (by decide) 2).inv singleton :=
    (a.run_correct _ (Memory.zeroAbove_init [31]) (by decide) hv).2.2.1
  exact ⟨by decide, hi.1, 31, by decide, hi.2⟩

private theorem zero_wellFormed : Memory.WellFormed 3 emptyZero := by
  have hv : (Memory.spec 3).ValidHistory (Memory.State.init [7])
      ((Memory.spec 3).clientHistory (Memory.State.init [7])
        ((zeroAllocator (n := 0) (K := 7) (w := 3) (by decide) (by decide)).run (pure ()))) :=
    by decide
  have h := (Memory.wellFormed_init (by decide) (by decide) :
    Memory.WellFormed 3 (Memory.State.init [7])).run hv
  rw [StateTransitionSpec.run_runClient] at h
  exact h

private theorem singleton_wellFormed : Memory.WellFormed 5 singleton := by
  have hv : (Memory.spec 5).ValidHistory (Memory.State.init [31])
      ((Memory.spec 5).clientHistory (Memory.State.init [31])
        ((zeroAllocator (n := 1) (K := 31) (w := 5) (by decide) (by decide)).run
          ((indexedMinPQSpec 1 31).call (.insert 0 31)))) := by decide
  have h := (Memory.wellFormed_init (by decide) (by decide) :
    Memory.WellFormed 5 (Memory.State.init [31])).run hv
  rw [StateTransitionSpec.run_runClient] at h
  exact h

/-- The full original heap domain is inhabited at all three boundary/structural clients. -/
theorem valid_cases : extractValid 3 ![0, 2] emptyZero ∧
    extractValid 5 ![1, 2] singleton ∧ extractValid 6 ![3, 2] consolidated :=
  ⟨zero_valid, singleton_valid,
    by exact ⟨by decide, consolidated_inv.1, 63, by decide, consolidated_inv.2⟩⟩

noncomputable section

private abbrev slots := 3 + realizes_extractRaw.scratchSize + 1
private abbrev regs := 3 + slots
private def frontier : Fin regs := ⟨2, by unfold regs; omega⟩
private def source (i : Fin 2) : Fin regs := ⟨i, by unfold regs; omega⟩
private def scratch (i : Fin slots) : Fin regs := ⟨3 + i, by unfold regs; omega⟩
private def out (i : Fin 3) : Fin regs :=
  scratch (Fin.castAdd (realizes_extractRaw.scratchSize + 1) i)

private def loaded (n base : ℕ) (mem : Memory.State) : Data regs where
  regs i := if i = frontier then mem.frontier else if i.val = 0 then n
    else if i.val = 1 then base else 0
  mem := mem.mem

private theorem native_extract {n base w : ℕ} {mem : Memory.State}
    (hw : Memory.WellFormed w mem) (hSafe : extractValid w ![n, base] mem)
    (hv : (Memory.spec w).ValidHistory mem ((Memory.spec w).clientHistory mem
      (Cslib.DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (extractRaw n)))) :
    ∃ y, ExecWithin w (realizes_extractRaw.code frontier source scratch) (loaded n base mem) y
        ((memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
          (extractRaw n)) mem + 1) * realizes_extractRaw.factor) ∧
      memoryState frontier y = (Memory.spec w).clientState mem
        (Cslib.DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (extractRaw n)) ∧
      ∀ i : Fin 3, y.regs (scratch (Fin.castAdd (realizes_extractRaw.scratchSize + 1) i)) =
        WordEncoding.encode (α := Option (ℕ × ℕ))
          ((Memory.spec w).clientResult mem
            (Cslib.DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
              (extractRaw n))) i := by
  have hi : Function.Injective scratch := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    simpa only [scratch, Nat.add_left_cancel_iff] using this
  have hd : ∀ i j, source i ≠ scratch j := by
    intro i j h
    have := congrArg Fin.val h
    simp only [source, scratch] at this
    have := i.isLt
    omega
  have hf : ∀ j, scratch j ≠ frontier := by
    intro j h
    have := congrArg Fin.val h
    simp only [scratch, frontier] at this
    omega
  have hs : ∀ i, source i ≠ frontier := by
    intro i h
    have := congrArg Fin.val h
    simp only [source, frontier] at this
    have := i.isLt
    omega
  have hFit : Fits w (base + (9 * n + 5)) := hSafe.1
  have hb : (loaded n base mem).Bounded w := by
    refine ⟨fun i => ?_, hw.mem_fits⟩
    dsimp only [loaded]
    split_ifs
    · exact hw.frontier_fits
    · exact hFit.of_le (by omega)
    · exact hFit.of_le (by omega)
    · exact fits_zero w
  have hin : (loaded n base mem).regs ∘ source = (![n, base] : Fin 2 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hp : memoryState frontier (loaded n base mem) = mem := rfl
  have hspec := (realizes_extractRaw.code_spec frontier source scratch hi hd hf hs).2 w
    (![n, base] : Fin 2 → ℕ) (loaded n base mem) hb hin
  rw [hp] at hspec
  obtain ⟨y, hy, hm, hout, _⟩ := hspec hSafe hv
  exact ⟨y, by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.add_zero, Nat.mul_comm] using hy, hm, hout⟩

/-- Zero capacity at width three returns the canonical absent result with one actual query. -/
example : ∃ y, ExecWithin 3 (realizes_extractRaw.code frontier source scratch)
      (loaded 0 2 emptyZero) y (2 * realizes_extractRaw.factor) ∧
    (∀ i : Fin 3, y.regs (scratch (Fin.castAdd (realizes_extractRaw.scratchSize + 1) i)) = 0) ∧
    y.mem = emptyZero.mem ∧ y.regs frontier = 7 := by
  obtain ⟨y, hy, hm, hout⟩ := native_extract zero_wellFormed zero_valid (by decide)
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 0 2).methods 0)
      (extractRaw 0)) emptyZero = 1 := by decide
  rw [hc] at hy
  refine ⟨y, hy, ?_, ?_, ?_⟩
  · intro i
    exact (hout i).trans (by fin_cases i <;> rfl)
  · exact congrArg Memory.State.mem hm
  · exact congrArg Memory.State.frontier hm

/-- The maximum five-bit key is returned unchanged, rather than shifted by a sentinel encoding. -/
example : ∃ y, ExecWithin 5 (realizes_extractRaw.code frontier source scratch)
      (loaded 1 2 singleton) y (13 * realizes_extractRaw.factor) ∧
    y.regs (out 0) = 1 ∧ y.regs (out 1) = 0 ∧ y.regs (out 2) = 31 ∧
    y.mem 1 = 31 ∧ y.regs frontier = 16 := by
  obtain ⟨y, hy, hm, hout⟩ := native_extract singleton_wellFormed singleton_valid (by decide)
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 1 2).methods 0)
      (extractRaw 1)) singleton = 12 := by decide
  rw [hc] at hy
  exact ⟨y, hy, (hout 0).trans (by decide), (hout 1).trans (by decide),
    (hout 2).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩

/-- A real child is detached, prepared, scattered and gathered by the complete native method. -/
example : ∃ y, ExecWithin 6 (realizes_extractRaw.code frontier source scratch)
      (loaded 3 2 consolidated) y (29 * realizes_extractRaw.factor) ∧
    y.regs (out 0) = 1 ∧ y.regs (out 1) = 1 ∧ y.regs (out 2) = 5 ∧
    y.mem 30 = 3 ∧ y.mem 7 = 0 ∧ y.mem 33 = 1 ∧ y.mem 1 = 63 ∧ y.regs frontier = 34 := by
  have hSafe : extractValid 6 ![3, 2] consolidated :=
    ⟨by decide, consolidated_inv.1, 63, by decide, consolidated_inv.2⟩
  obtain ⟨y, hy, hm, hout⟩ := native_extract consolidated_wellFormed hSafe (by decide)
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
      (extractRaw 3)) consolidated = 28 := by decide
  rw [hc] at hy
  exact ⟨y, hy, (hout 0).trans (by decide), (hout 1).trans (by decide),
    (hout 2).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 30).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 7).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 33).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩

end

end ComplexityTests.FibonacciHeapNativeExtract
