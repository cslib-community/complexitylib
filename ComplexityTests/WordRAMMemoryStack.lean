/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Realization.Client.MemoryStack

/-! Concrete native instances of the unchanged stack methods. The pop uses the largest four-bit
payload, so a successor-based option encoding could not satisfy this instance. Both methods retain
the literal inaccessible memory. These instruction bounds include certified local work. -/

namespace ComplexityTests.WordRAMMemoryStack

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open MemoryStack

private def front {k t : ℕ} : Fin (1 + (k + t)) := ⟨0, by omega⟩
private def src {k t : ℕ} (i : Fin k) : Fin (1 + (k + t)) :=
  Fin.natAdd 1 (Fin.castAdd t i)
private def tmp {k t : ℕ} (i : Fin t) : Fin (1 + (k + t)) := Fin.natAdd 1 (Fin.natAdd k i)

private theorem layout (k t : ℕ) :
    Function.Injective (tmp (k := k) (t := t)) ∧
      (∀ i j, src (t := t) i ≠ tmp (k := k) j) ∧
      (∀ j, tmp (k := k) (t := t) j ≠ front) ∧
      (∀ i, src (k := k) (t := t) i ≠ front) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    simp only [tmp, Fin.val_natAdd] at this
    omega
  · intro i j h
    have := congrArg Fin.val h
    simp only [src, tmp, Fin.val_natAdd, Fin.val_castAdd] at this
    have := i.isLt
    omega
  · intro i h
    have := congrArg Fin.val h
    simp only [tmp, front, Fin.val_natAdd] at this
    omega
  · intro i h
    have := congrArg Fin.val h
    simp only [src, front, Fin.val_natAdd, Fin.val_castAdd] at this
    omega

private def packed {k t : ℕ} (v : Fin k → ℕ) (s : Memory.State) : Data (1 + (k + t)) :=
  ⟨Fin.addCases (fun _ => s.frontier) (Fin.addCases v (fun _ => 0)), s.mem⟩

private theorem packed_bounded {k t w : ℕ} {v : Fin k → ℕ} {s : Memory.State}
    (hv : ∀ i, Fits w (v i)) (hs : Memory.WellFormed w s) :
    (packed (t := t) v s).Bounded w := by
  refine ⟨fun i => ?_, hs.mem_fits⟩
  refine Fin.addCases (fun _ => by simpa [packed] using hs.frontier_fits) (fun j => ?_) i
  exact Fin.addCases (fun i => by simpa [packed] using hv i)
    (fun _ => by simp [packed]) j

private theorem packed_input {k t : ℕ} (v : Fin k → ℕ) (s : Memory.State) :
    (packed (t := t) v s).regs ∘ src = v := by
  funext i
  simp [packed, src]

private theorem packed_state {k t : ℕ} (v : Fin k → ℕ) (s : Memory.State) :
    memoryState front (packed (t := t) v s) = s := by
  cases s
  rfl

private def L : Stack.Memory.Layout := ⟨⟨2, 1⟩, ⟨3, 2⟩⟩
private def empty : Memory.State := ⟨fun a => if a = 2 then 0 else 7, 8⟩
private def singleton : Memory.State :=
  ⟨fun a => if a = 2 then 1 else if a = 3 then 15 else 7, 8⟩

private theorem valid_layout : L.Valid 4 2 := by
  refine ⟨rfl, ?_, rfl, by decide⟩
  change ¬(3 ≤ 2 ∧ 2 < 3 + 2)
  omega

private theorem empty_inv : Stack.Memory.Inv L empty := by
  constructor
  · change 2 + 1 ≤ 8; decide
  · change 3 + 2 ≤ 8; decide
  · change 0 ≤ 2; decide

private theorem singleton_inv : Stack.Memory.Inv L singleton := by
  constructor
  · change 2 + 1 ≤ 8; decide
  · change 3 + 2 ≤ 8; decide
  · change 1 ≤ 2; decide

private theorem empty_wf : Memory.WellFormed 4 empty := by
  refine ⟨by decide, fun a => ?_⟩
  change Fits 4 (if a = 2 then 0 else 7)
  split <;> decide

private theorem singleton_wf : Memory.WellFormed 4 singleton := by
  refine ⟨by decide, fun a => ?_⟩
  change Fits 4 (if a = 2 then 1 else if a = 3 then 15 else 7)
  split
  · decide
  · split <;> decide

-- A maximum-word push executes the generic certificate on a complete runtime layout.
example : ∃ r C, ∃ (code : Code .exact r) (x y : Data r),
    ExecWithin 4 code x y (C * 14) ∧ y.mem 3 = 15 ∧ y.mem 10 = 7 := by
  obtain ⟨n, C, emit, he⟩ := realizes_push
  let x := packed (t := 0 + n + 1) (pushWords (L, 15)) empty
  obtain ⟨hi, hd, hf, hs⟩ := layout 5 (0 + n + 1)
  have hx : x.Bounded 4 := packed_bounded (by intro i; fin_cases i <;> decide) empty_wf
  have hin := packed_input (t := 0 + n + 1) (pushWords (L, 15)) empty
  have hm := packed_state (t := 0 + n + 1) (pushWords (L, 15)) empty
  have hsafe : L.Valid 4 L.items.length ∧ Stack.Memory.Inv L (memoryState front x) ∧
      (memoryState front x).mem L.count.base < L.items.length := by
    rw [hm]
    exact ⟨valid_layout, empty_inv, by decide⟩
  have hv : (Memory.spec 4).ValidHistory (memoryState front x)
      ((Memory.spec 4).clientHistory (memoryState front x) (Stack.Memory.push L 15)) := by
    rw [hm]
    decide
  obtain ⟨y, hy, hmem, _, _⟩ := (he front src tmp hi hd hf hs).2 4 (L, 15) x hx hin hsafe hv
  rw [hm] at hy hmem
  refine ⟨_, C, emit front src tmp, x, y, hy, ?_, ?_⟩
  · exact congrArg (fun s : Memory.State => s.mem 3) hmem
  · exact congrArg (fun s : Memory.State => s.mem 10) hmem

-- One native pop body handles both actual branches. The positive branch returns the maximum
-- word as (tag=1,payload=15), while the empty branch returns (0,0).
example : ∃ r C, ∃ (code : Code .exact r) (x y x₀ y₀ : Data r) (tag payload : Fin r),
    ExecWithin 4 code x y (C * 23) ∧ y.regs tag = 1 ∧ y.regs payload = 15 ∧
      y.mem 2 = 0 ∧ y.mem 10 = 7 ∧ ExecWithin 4 code x₀ y₀ (C * 21) ∧
      y₀.regs tag = 0 ∧ y₀.regs payload = 0 ∧ y₀.mem 10 = 7 := by
  obtain ⟨n, C, emit, he⟩ := realizes_pop
  let x := packed (t := 2 + n + 1) (layoutWords L) singleton
  obtain ⟨hi, hd, hf, hs⟩ := layout 4 (2 + n + 1)
  have hx : x.Bounded 4 := packed_bounded (by intro i; fin_cases i <;> decide) singleton_wf
  have hin := packed_input (t := 2 + n + 1) (layoutWords L) singleton
  have hm := packed_state (t := 2 + n + 1) (layoutWords L) singleton
  have hsafe : L.Valid 4 L.items.length ∧ Stack.Memory.Inv L (memoryState front x) := by
    rw [hm]
    exact ⟨valid_layout, singleton_inv⟩
  have hv : (Memory.spec 4).ValidHistory (memoryState front x)
      ((Memory.spec 4).clientHistory (memoryState front x) (Stack.Memory.pop L)) := by
    rw [hm]
    decide
  obtain ⟨y, hy, hmem, hout, _⟩ := (he front src tmp hi hd hf hs).2 4 L x hx hin hsafe hv
  rw [hm] at hy hmem hout
  let x₀ := packed (t := 2 + n + 1) (layoutWords L) empty
  have hx₀ : x₀.Bounded 4 := packed_bounded (by intro i; fin_cases i <;> decide) empty_wf
  have hin₀ := packed_input (t := 2 + n + 1) (layoutWords L) empty
  have hm₀ := packed_state (t := 2 + n + 1) (layoutWords L) empty
  have hsafe₀ : L.Valid 4 L.items.length ∧ Stack.Memory.Inv L (memoryState front x₀) := by
    rw [hm₀]
    exact ⟨valid_layout, empty_inv⟩
  have hv₀ : (Memory.spec 4).ValidHistory (memoryState front x₀)
      ((Memory.spec 4).clientHistory (memoryState front x₀) (Stack.Memory.pop L)) := by
    rw [hm₀]
    decide
  obtain ⟨y₀, hy₀, hmem₀, hout₀, _⟩ :=
    (he front src tmp hi hd hf hs).2 4 L x₀ hx₀ hin₀ hsafe₀ hv₀
  rw [hm₀] at hy₀ hmem₀ hout₀
  refine ⟨_, C, emit front src tmp, x, y, x₀, y₀, tmp (Fin.castAdd (n + 1) 0),
    tmp (Fin.castAdd (n + 1) 1), hy, hout 0, hout 1, ?_, ?_, hy₀, hout₀ 0, hout₀ 1, ?_⟩
  · exact congrArg (fun s : Memory.State => s.mem 2) hmem
  · exact congrArg (fun s : Memory.State => s.mem 10) hmem
  · exact congrArg (fun s : Memory.State => s.mem 10) hmem₀

-- The empty path is semantically none and uses a valid, non-vacuous layout and memory state.
example : (Memory.spec 4).clientResult empty (Stack.Memory.pop L) = none := by decide

example : optionWords (some 15) = ![1, 15] ∧ Fits 4 15 ∧ ¬Fits 4 (15 + 1) := by decide

end ComplexityTests.WordRAMMemoryStack
