/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Realization.Primitive

/-!
# Concrete clients of native memory-query realization

The clients instantiate the emitted native code on dirty memory, retain an unrelated live word,
and inspect the returned word, frontier and entire resulting memory. Empty zeroed allocation is
also instantiated at word width zero, where the constant `1` cannot be written.
-/

namespace ComplexityTests.WordRAMRealizationPrimitive

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure

private abbrev wordWords : ℕ ↪ (Fin 1 → ℕ) :=
  Equiv.toEmbedding (Equiv.symm (Equiv.funUnique (Fin 1) ℕ))

private def initial {r : ℕ} (frontier arg marker : ℕ) (mem : ℕ → ℕ) : Data r :=
  ⟨fun j => if j.val = 0 then frontier else if j.val = 1 then arg
    else if j.val = 2 then marker else 0, mem⟩

/-- A canonical layout keeps the frontier, argument and a live marker before the fresh bank. -/
private theorem word_query {B : Basis} (p : ℕ → Memory.Prog ℕ)
    (h : Realizes B p wordWords wordWords (fun _ _ _ => True) (fun _ _ => 0))
    (w frontier arg marker : ℕ) (mem : ℕ → ℕ)
    (hf : Fits w frontier) (ha : Fits w arg) (hm : ∀ a, Fits w (mem a))
    (hmarker : Fits w marker)
    (hv : (Memory.spec w).ValidHistory ⟨mem, frontier⟩
      ((Memory.spec w).clientHistory ⟨mem, frontier⟩ (p arg))) :
    ∃ n C, ∃ code : Code B (3 + (1 + n + 1)), ∃ y : Data (3 + (1 + n + 1)),
      ExecWithin w code (initial frontier arg marker mem) y
        (C * (memoryCost (p arg) ⟨mem, frontier⟩ + 1)) ∧
      memoryState ⟨0, by omega⟩ y = (Memory.spec w).clientState ⟨mem, frontier⟩ (p arg) ∧
      y.regs ⟨3, by omega⟩ = (Memory.spec w).clientResult ⟨mem, frontier⟩ (p arg) ∧
      y.regs ⟨1, by omega⟩ = arg ∧ y.regs ⟨2, by omega⟩ = marker := by
  obtain ⟨n, C, emit, he⟩ := h
  let f : Fin (3 + (1 + n + 1)) := ⟨0, by omega⟩
  let src : Fin 1 → Fin (3 + (1 + n + 1)) := fun _ => ⟨1, by omega⟩
  let tmp : Fin (1 + n + 1) → Fin (3 + (1 + n + 1)) := Fin.natAdd 3
  have hi : Function.Injective tmp := by
    intro a b hab
    apply Fin.ext
    have hval := congrArg Fin.val hab
    change 3 + a.val = 3 + b.val at hval
    omega
  have hd (i : Fin 1) (j : Fin (1 + n + 1)) : src i ≠ tmp j := by
    intro hij
    have hval := congrArg Fin.val hij
    change 1 = 3 + j.val at hval
    omega
  have htf (j : Fin (1 + n + 1)) : tmp j ≠ f := by
    intro hj
    have hval := congrArg Fin.val hj
    change 3 + j.val = 0 at hval
    omega
  have hsf (i : Fin 1) : src i ≠ f := by
    intro hi
    have hval := congrArg Fin.val hi
    change 1 = 0 at hval
    omega
  let x : Data (3 + (1 + n + 1)) := initial frontier arg marker mem
  have hx : x.Bounded w := by
    refine ⟨fun j => ?_, hm⟩
    change Fits w (if j.val = 0 then frontier else if j.val = 1 then arg
      else if j.val = 2 then marker else 0)
    split_ifs <;> first | exact hf | exact ha | exact hmarker | exact fits_zero w
  have hin : x.regs ∘ src = wordWords arg := by
    funext i
    rfl
  obtain ⟨y, hy, hstate, hout, hframe⟩ := (he f src tmp hi hd htf hsf).2 w arg x hx hin
    trivial hv
  have hxs : memoryState f x = ⟨mem, frontier⟩ := rfl
  rw [hxs] at hy hstate hout
  have ho := hout 0
  change y.regs ⟨3, by omega⟩ = (Memory.spec w).clientResult ⟨mem, frontier⟩ (p arg) at ho
  have harg := hframe ⟨1, by omega⟩
    (by intro h; have hval := congrArg Fin.val h; change 1 = 0 at hval; omega)
    (fun j h => by have hval := congrArg Fin.val h; change 3 + j.val = 1 at hval; omega)
  have hmark := hframe ⟨2, by omega⟩
    (by intro h; have hval := congrArg Fin.val h; change 2 = 0 at hval; omega)
    (fun j h => by have hval := congrArg Fin.val h; change 3 + j.val = 2 at hval; omega)
  refine ⟨n, C, emit f src tmp, y, ?_, hstate, ho, harg, hmark⟩
  simpa only [Nat.add_zero] using hy

-- Clearing a dirty block preserves both the allocated prefix and inaccessible high cells.
example :
    ∃ n C, ∃ code : Code .exact (3 + (1 + n + 1)), ∃ y : Data (3 + (1 + n + 1)),
      ExecWithin 4 code (initial 3 2 9 (fun _ => 7)) y (C * 4) ∧
      y.regs ⟨0, by omega⟩ = 5 ∧ y.regs ⟨3, by omega⟩ = 3 ∧
      y.regs ⟨1, by omega⟩ = 2 ∧ y.regs ⟨2, by omega⟩ = 9 ∧
      y.mem 3 = 0 ∧ y.mem 4 = 0 ∧ y.mem 2 = 7 ∧ y.mem 100 = 7 := by
  obtain ⟨n, C, code, y, he, hs, ho, ha, hl⟩ :=
    word_query Memory.alloc (Realizes.alloc wordWords 0) 4 3 2 9 (fun _ => 7)
      (by norm_num [Fits]) (by norm_num [Fits]) (fun _ => by norm_num [Fits])
      (by norm_num [Fits]) (by change Fits 4 (3 + 2) ∧ True; norm_num [Fits])
  have hf := congrArg Memory.State.frontier hs
  have hm := congrArg Memory.State.mem hs
  change y.mem = clear (fun _ => 7) 3 2 at hm
  refine ⟨n, C, code, y, he, hf, ho, ha, hl, ?_⟩
  rw [hm]
  norm_num [clear]

-- At width zero only zero fits, but allocating an empty block still has a native realization.
example :
    ∃ n C, ∃ code : Code .exact (3 + (1 + n + 1)), ∃ y : Data (3 + (1 + n + 1)),
      ExecWithin 0 code (initial 0 0 0 (fun _ => 0)) y (C * 2) ∧
      y.regs ⟨0, by omega⟩ = 0 ∧ y.regs ⟨3, by omega⟩ = 0 ∧
      y.mem = (fun _ => 0) ∧ y.regs ⟨2, by omega⟩ = 0 := by
  obtain ⟨n, C, code, y, he, hs, ho, _, hl⟩ :=
    word_query Memory.alloc (Realizes.alloc wordWords 0) 0 0 0 0 (fun _ => 0)
      (fits_zero 0) (fits_zero 0) (fun _ => fits_zero 0) (fits_zero 0)
      (by change Fits 0 (0 + 0) ∧ True; exact ⟨fits_zero 0, trivial⟩)
  have hf := congrArg Memory.State.frontier hs
  have hm := congrArg Memory.State.mem hs
  change y.mem = clear (fun _ => 0) 0 0 at hm
  rw [clear_zero] at hm
  exact ⟨n, C, code, y, he, hf, ho, hm, hl⟩

-- Dirty allocation retains every old memory value while returning the old frontier.
example :
    ∃ n C, ∃ code : Code .exact (3 + (1 + n + 1)), ∃ y : Data (3 + (1 + n + 1)),
      ExecWithin 4 code (initial 3 2 9 (fun _ => 7)) y (C * 2) ∧
      y.regs ⟨0, by omega⟩ = 5 ∧ y.regs ⟨3, by omega⟩ = 3 ∧
      y.mem = (fun _ => 7) ∧ y.regs ⟨2, by omega⟩ = 9 := by
  obtain ⟨n, C, code, y, he, hs, ho, _, hl⟩ :=
    word_query Memory.allocDirty (Realizes.allocDirty wordWords 0) 4 3 2 9 (fun _ => 7)
      (by norm_num [Fits]) (by norm_num [Fits]) (fun _ => by norm_num [Fits])
      (by norm_num [Fits]) (by change Fits 4 (3 + 2) ∧ True; norm_num [Fits])
  exact ⟨n, C, code, y, he, congrArg Memory.State.frontier hs, ho,
    congrArg Memory.State.mem hs, hl⟩

-- Reading an allocated word keeps the entire dirty memory and an unrelated live register.
example :
    ∃ n C, ∃ code : Code .exact (3 + (1 + n + 1)), ∃ y : Data (3 + (1 + n + 1)),
      ExecWithin 4 code (initial 3 2 9 (fun _ => 7)) y (C * 2) ∧
      y.regs ⟨0, by omega⟩ = 3 ∧ y.regs ⟨3, by omega⟩ = 7 ∧
      y.mem = (fun _ => 7) ∧ y.regs ⟨2, by omega⟩ = 9 := by
  obtain ⟨n, C, code, y, he, hs, ho, _, hl⟩ :=
    word_query Memory.read (Realizes.read (B := .exact) wordWords 0) 4 3 2 9 (fun _ => 7)
      (by norm_num [Fits]) (by norm_num [Fits]) (fun _ => by norm_num [Fits])
      (by norm_num [Fits]) (by change 2 < 3 ∧ True; norm_num)
  exact ⟨n, C, code, y, he, congrArg Memory.State.frontier hs, ho,
    congrArg Memory.State.mem hs, hl⟩

private def pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) where
  toFun x := ![x.1, x.2]
  inj' := by
    intro a b h
    apply Prod.ext
    · exact congrFun h 0
    · exact congrFun h 1

private def writeInitial {r : ℕ} : Data r :=
  ⟨fun j => if j.val = 0 then 3 else if j.val = 1 then 2 else if j.val = 2 then 12 else 9,
    fun _ => 7⟩

-- A store changes its allocated cell while preserving low/high memory and a live register.
example :
    ∃ n C, ∃ code : Code .exact (4 + (0 + n + 1)), ∃ y : Data (4 + (0 + n + 1)),
      ExecWithin 4 code writeInitial y (C * 2) ∧
      y.regs ⟨0, by omega⟩ = 3 ∧ y.mem 2 = 12 ∧ y.mem 0 = 7 ∧ y.mem 100 = 7 ∧
      y.regs ⟨3, by omega⟩ = 9 := by
  obtain ⟨n, C, emit, he⟩ := Realizes.write (B := .exact) pairWords 0 1
  let f : Fin (4 + (0 + n + 1)) := ⟨0, by omega⟩
  let src : Fin 2 → Fin (4 + (0 + n + 1)) := fun i => ⟨1 + i.val, by omega⟩
  let tmp : Fin (0 + n + 1) → Fin (4 + (0 + n + 1)) := Fin.natAdd 4
  have hi : Function.Injective tmp := by
    intro a b hab
    apply Fin.ext
    have hval := congrArg Fin.val hab
    change 4 + a.val = 4 + b.val at hval
    omega
  have hd (i : Fin 2) (j : Fin (0 + n + 1)) : src i ≠ tmp j := by
    intro hij
    have hval := congrArg Fin.val hij
    change 1 + i.val = 4 + j.val at hval
    omega
  have htf (j : Fin (0 + n + 1)) : tmp j ≠ f := by
    intro hj
    have hval := congrArg Fin.val hj
    change 4 + j.val = 0 at hval
    omega
  have hsf (i : Fin 2) : src i ≠ f := by
    intro hi
    have hval := congrArg Fin.val hi
    change 1 + i.val = 0 at hval
    omega
  let x : Data (4 + (0 + n + 1)) := writeInitial
  have hx : x.Bounded 4 := by
    refine ⟨fun j => ?_, fun _ => by change Fits 4 7; norm_num [Fits]⟩
    change Fits 4 (if j.val = 0 then 3 else if j.val = 1 then 2 else if j.val = 2 then 12 else 9)
    split_ifs <;> norm_num [Fits]
  have hin : x.regs ∘ src = pairWords (2, 12) := by
    funext i
    fin_cases i <;> rfl
  have hv : (Memory.spec 4).ValidHistory (memoryState f x)
      ((Memory.spec 4).clientHistory (memoryState f x) (Memory.write 2 12)) := by
    change (2 < 3 ∧ Fits 4 12) ∧ True
    norm_num [Fits]
  obtain ⟨y, hy, hs, _, hframe⟩ := (he f src tmp hi hd htf hsf).2 4 (2, 12) x hx hin trivial hv
  have hm := congrArg Memory.State.mem hs
  change y.mem = Function.update (fun _ => 7) 2 12 at hm
  have hf := congrArg Memory.State.frontier hs
  have hl := hframe ⟨3, by omega⟩
    (by intro h; have hval := congrArg Fin.val h; change 3 = 0 at hval; omega)
    (fun j h => by have hval := congrArg Fin.val h; change 4 + j.val = 3 at hval; omega)
  refine ⟨n, C, emit f src tmp, y, hy, hf, ?_, ?_, ?_, hl⟩ <;> rw [hm] <;> norm_num

end ComplexityTests.WordRAMRealizationPrimitive
