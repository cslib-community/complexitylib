/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression client for static input reindexing)

public import CslibFrontier.Computability.WordRAM.Realization.Primitive
public import CslibFrontier.Computability.WordRAM.Realization.Reindex

/-!
# Re-layout a memory read without runtime computation

The original one-word read certificate selects the second word of a larger faithful
environment. Native execution returns the maximal four-bit word, retains the unused first
input and the entire memory/frontier, and pays the unchanged memory-query charge.
-/

public section

namespace Cslib.WordRAM.Realization.Tests.Reindex

open Cslib.DataStructure

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
private abbrev environment : ℕ × ℕ ↪ (Fin 2 → ℕ) := appendWords word word

private theorem readSecond :
    Realizes .exact (fun d : ℕ × ℕ => Memory.read d.2) environment word
      (fun _ _ _ => True) (fun _ _ => 0) :=
  (Realizes.read word 0).reindex Prod.snd environment ![1]
    (by intro d i; fin_cases i; rfl)

/-- Reindexing preserves the unused input word and the inaccessible memory tail. -/
theorem readSecond_native : ∃ r C, ∃ code : Code .exact r, ∃ x y : Data r,
    ∃ result tag frontier : Fin r,
      x.Bounded 4 ∧ x.regs tag = 7 ∧
      ExecWithin 4 code x y (C * 2) ∧ y.regs result = 15 ∧ y.regs tag = 7 ∧
      y.mem 100 = 5 ∧ y.regs frontier = 4 ∧ ¬code.ReadsWidth := by
  obtain ⟨n, C, emit, he⟩ := readSecond
  let r := 3 + (1 + n + 1)
  let frontier : Fin r := ⟨0, by omega⟩
  let src : Fin 2 → Fin r := fun i => ⟨1 + i.val, by omega⟩
  let tmp : Fin (1 + n + 1) → Fin r := fun i => ⟨3 + i.val, by omega⟩
  have hi : Function.Injective tmp := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp only [tmp] at this
    omega
  have hd (i : Fin 2) (j : Fin (1 + n + 1)) : src i ≠ tmp j := by
    intro h
    have := congrArg Fin.val h
    dsimp only [src, tmp] at this
    have := i.isLt
    omega
  have hf (j : Fin (1 + n + 1)) : tmp j ≠ frontier := by
    intro h
    have := congrArg Fin.val h
    dsimp only [tmp, frontier] at this
    omega
  have hs (i : Fin 2) : src i ≠ frontier := by
    intro h
    have := congrArg Fin.val h
    dsimp only [src, frontier] at this
    omega
  let x : Data r := ⟨fun i => if i = src 0 then 7 else if i = src 1 then 2 else
    if i = frontier then 4 else 0, fun a => if a = 2 then 15 else 5⟩
  have hx : x.Bounded 4 := by
    constructor
    · intro i
      change Fits 4 (if i = src 0 then 7 else if i = src 1 then 2 else
        if i = frontier then 4 else 0)
      split_ifs <;> decide
    · intro a
      change Fits 4 (if a = 2 then 15 else 5)
      split_ifs <;> decide
  have hin : x.regs ∘ src = environment (7, 2) := by
    funext i
    fin_cases i <;> rfl
  have hm : memoryState frontier x =
      (⟨fun a => if a = 2 then 15 else 5, 4⟩ : Memory.State) := rfl
  have hv : (Memory.spec 4).ValidHistory (memoryState frontier x)
      ((Memory.spec 4).clientHistory (memoryState frontier x) (Memory.read 2)) := by
    rw [hm]
    decide
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  obtain ⟨y, hy, hmem, hout, hframe⟩ := hrun 4 (7, 2) x hx hin trivial hv
  rw [hm] at hy hmem hout
  have htag := hframe (src 0) (hs 0) (fun j => (hd 0 j).symm)
  refine ⟨r, C, emit frontier src tmp, x, y, tmp 0, src 0, frontier, hx, ?_, hy,
    hout 0, ?_, congrArg (fun s : Memory.State => s.mem 100) hmem,
    congrArg Memory.State.frontier hmem, hnw⟩
  · simp [x]
  · simpa [x] using htag

end Cslib.WordRAM.Realization.Tests.Reindex
