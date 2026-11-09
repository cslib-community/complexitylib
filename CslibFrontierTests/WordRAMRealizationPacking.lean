/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.WordRAM.Realization.Witness

/-! A shared static installed-register fixture for native realization tests. This only places
arguments, scratch and the frontier and applies the existing kernel contract; it performs no
client instruction execution or algorithm-specific frame proof. -/

namespace CslibFrontierTests.WordRAMRealizationPacking

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure

noncomputable section

variable {δ α : Type} {k l : ℕ} {p : δ → Memory.Prog α}
  {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
  {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}

abbrev bankSize (h : Realizes .exact p input output safe work) := l + h.scratchSize + 1
abbrev regs (h : Realizes .exact p input output safe work) := k + bankSize h + 1
def frontier (h : Realizes .exact p input output safe work) : Fin (regs h) :=
  Fin.last (k + bankSize h)
def src (h : Realizes .exact p input output safe work) (i : Fin k) : Fin (regs h) :=
  (Fin.castAdd (bankSize h) i).castSucc
def tmp (h : Realizes .exact p input output safe work) (i : Fin (bankSize h)) :
    Fin (regs h) := (Fin.natAdd k i).castSucc
def packed (h : Realizes .exact p input output safe work) (d : δ) (s : Memory.State) :
    Data (regs h) :=
  ⟨Fin.lastCases s.frontier (Fin.append (input d) (fun _ => 0)), s.mem⟩

theorem packed_state (h : Realizes .exact p input output safe work) (d : δ)
    (s : Memory.State) : memoryState (frontier h) (packed h d s) = s := by
  cases s
  simp [memoryState, frontier, packed]

theorem native (h : Realizes .exact p input output safe work) (w : ℕ) (d : δ)
    (s : Memory.State) (hw : ∀ i, Fits w (input d i)) (hm : Memory.WellFormed w s)
    (hs : safe w d s)
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d))) :
    ∃ y, ExecWithin w (h.code (frontier h) (src h) (tmp h)) (packed h d s) y
        (h.factor * (memoryCost (p d) s + work d s + 1)) ∧
      memoryState (frontier h) y = (Memory.spec w).clientState s (p d) ∧
      ∀ i : Fin l, y.regs (tmp h (Fin.castAdd (h.scratchSize + 1) i)) =
        output ((Memory.spec w).clientResult s (p d)) i := by
  have hi : Function.Injective (tmp h) := by
    intro i j he
    apply Fin.ext
    have hh := congrArg Fin.val he
    simpa [tmp] using hh
  have hd : ∀ i j, src h i ≠ tmp h j := by
    intro i j he
    have hh := congrArg Fin.val he
    dsimp only [src, tmp, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd] at hh
    omega
  have hf : ∀ j, tmp h j ≠ frontier h := by
    intro j he
    have hh := congrArg Fin.val he
    dsimp only [tmp, frontier, Fin.val_castSucc, Fin.val_natAdd, Fin.val_last] at hh
    omega
  have hsrc : ∀ i, src h i ≠ frontier h := by
    intro i he
    have hh := congrArg Fin.val he
    dsimp only [src, frontier, Fin.val_castSucc, Fin.val_castAdd, Fin.val_last] at hh
    omega
  have hx : (packed h d s).Bounded w := by
    refine ⟨?_, hm.mem_fits⟩
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [packed] using hm.frontier_fits
    · simp only [packed, Fin.lastCases_castSucc]
      exact Fin.addCases (fun j => by simpa using hw j)
        (fun _ => by simp) i
  have hin : (packed h d s).regs ∘ src h = input d := by
    funext i
    simp [packed, src]
  obtain ⟨y, hy, hm, ho, _⟩ := (h.code_spec (frontier h) (src h) (tmp h) hi hd hf hsrc).2
    w d (packed h d s) hx hin (by simpa only [packed_state] using hs)
    (by simpa only [packed_state] using hv)
  exact ⟨y, by simpa only [packed_state] using hy,
    by simpa only [packed_state] using hm, by simpa only [packed_state] using ho⟩

end

end CslibFrontierTests.WordRAMRealizationPacking
