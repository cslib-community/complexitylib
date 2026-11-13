/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeaf
import Mathlib.Tactic.FinCases

/-!
# The physical layout of a carry-save leaf query

The six controller words occupy tapes zero through five, followed by context, count, and width.
All remaining tapes are blank. The persistent path head is at its right blank, the unary depth
head is at its frontier, and every other work head is zero. The host input head is at the left
blank, which is explicit in the bridge to `tapesCfg`.
-/

public section

namespace Turing.MultiTapeATM.CarrySaveLeafLayout

open MultiTapeTM

/-- Height, bit index, path, status, unary depth, empty flags, context, count, width, then
blank scratch words. -/
@[expose] def words (k : ℕ) (context count width height bits path unary : List Bool)
    (status : Bool) (i : Fin (k + 12)) : List Bool :=
  if i.val = 0 then height else if i.val = 1 then bits else if i.val = 2 then path
  else if i.val = 3 then [status] else if i.val = 4 then unary
  else if i.val = 6 then context else if i.val = 7 then count else if i.val = 8 then width
  else []

/-- The path is at its right blank and unary depth at its frontier; all other heads are zero. -/
@[expose] def heads (k : ℕ) (path : List Bool) (frontier : ℤ) (i : Fin (k + 12)) : ℤ :=
  if i.val = 2 then path.length else if i.val = 4 then frontier else 0

/-- The fresh carry tape and all evaluator scratch words are blank. -/
theorem words_scratch (k : ℕ) (context count width height bits path unary : List Bool)
    (status : Bool) (i : Fin (k + 12)) (hi : 9 ≤ i.val) :
    words k context count width height bits path unary status i = [] := by
  unfold words
  split_ifs <;> first | omega | rfl

private theorem words_core (k : ℕ) (context count width height bits path unary : List Bool)
    (status : Bool) (i : Fin 6) :
    words k context count width height bits path unary status (CarrySaveStream.coreEmb (k + 6) i) =
      ![height, bits, path, [status], unary, []] i := by
  fin_cases i <;> rfl

private theorem heads_core (k : ℕ) (path : List Bool) (frontier : ℤ) (i : Fin 6) :
    heads k path frontier (CarrySaveStream.coreEmb (k + 6) i) =
      ![0, 0, (path.length : ℤ), 0, frontier, 0] i := by
  fin_cases i <;> rfl

/-- Every initialized tape has exactly the corresponding named word. -/
theorem initial_tape (k : ℕ) (input context count width height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) (i : Fin (k + 12)) :
    (CarrySaveLeaf.initial k input context count width height bits path unary frontier
      status).workTapes i =
        tapeOfList (words k context count width height bits path unary status i) := by
  by_cases hi : i.val < 6
  · let j : Fin 6 := ⟨i.val, hi⟩
    have he : CarrySaveStream.coreEmb (k + 6) j = i := rfl
    rw [← he, words_core]
    exact CarrySaveStream.config_core_tape height bits path unary frontier status j
  · have hge : 6 ≤ i.val := by omega
    have h₀ : i.val ≠ 0 := by omega
    have h₁ : i.val ≠ 1 := by omega
    have h₂ : i.val ≠ 2 := by omega
    have h₃ : i.val ≠ 3 := by omega
    have h₄ : i.val ≠ 4 := by omega
    simp only [CarrySaveLeaf.initial, CarrySaveStream.config_extra_tape _ _ _ _ _ _ i hge,
      CarrySaveLeaf.scratch, words, h₀, h₁, h₂, h₃, h₄, ↓reduceIte]
    split_ifs <;> simp only [tapeOfList_nil]

/-- The initialized work heads agree with the path and frontier layout. -/
theorem initial_head (k : ℕ) (input context count width height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) (i : Fin (k + 12)) :
    (CarrySaveLeaf.initial k input context count width height bits path unary frontier
      status).workTapePos i = heads k path frontier i := by
  by_cases hi : i.val < 6
  · let j : Fin 6 := ⟨i.val, hi⟩
    have he : CarrySaveStream.coreEmb (k + 6) j = i := rfl
    rw [← he]
    change (CarrySaveStream.config height bits path unary frontier status
      (CarrySaveLeaf.scratch k context count width)).workTapePos _ = _
    rw [CarrySaveStream.config_core_head, heads_core]
  · have hge : 6 ≤ i.val := by omega
    have h₂ : i.val ≠ 2 := by omega
    have h₄ : i.val ≠ 4 := by omega
    simp [CarrySaveLeaf.initial, CarrySaveStream.config_extra_head _ _ _ _ _ _ i hge,
      CarrySaveLeaf.scratch, heads, h₂, h₄]

/-- The complete leaf storage is a word layout with the host input at its left blank. -/
theorem initial_eq_tapesCfg (k : ℕ)
    (input context count width height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) :
    CarrySaveLeaf.initial k input context count width height bits path unary frontier status =
      { tapesCfg input (words k context count width height bits path unary status)
          (fun _ => 0) (heads k path frontier) [] with inputPos := 0 } := by
  apply Cfg.ext
  · simp [CarrySaveLeaf.initial, tapesCfg]
  · simp [CarrySaveLeaf.initial]
  · funext i z
    simpa only [tapesCfg, Int.sub_zero] using
      congrFun (initial_tape k input context count width height bits path unary frontier status i) z
  · funext i
    exact initial_head k input context count width height bits path unary frontier status i
  · simp [CarrySaveLeaf.initial, tapesCfg]

/-- At an empty root path and zero frontier all work heads are at zero. -/
theorem initial_nil_eq_tapesCfg (k : ℕ)
    (input context count width height bits unary : List Bool) (status : Bool) :
    CarrySaveLeaf.initial k input context count width height bits [] unary 0 status =
      { tapesCfg input (words k context count width height bits [] unary status)
          (fun _ => 0) (fun _ => 0) [] with inputPos := 0 } := by
  have hh : heads k [] 0 = fun _ => 0 := by funext i; simp [heads]
  simpa only [hh] using
    initial_eq_tapesCfg k input context count width height bits [] unary 0 status

/-- Replacing tape zero changes precisely the binary height word. -/
theorem words_update_height (k : ℕ)
    (context count width height bits path unary height' : List Bool)
    (status : Bool) :
    Function.update (words k context count width height bits path unary status) 0 height' =
      words k context count width height' bits path unary status := by
  apply Function.update_eq_iff.mpr
  refine ⟨rfl, fun i hi => ?_⟩
  have hv : i.val ≠ 0 := fun h => hi (Fin.ext h)
  simp [words, hv]

/-- Replacing tape one changes precisely the binary queried-bit word. -/
theorem words_update_bits (k : ℕ) (context count width height bits path unary bits' : List Bool)
    (status : Bool) :
    Function.update (words k context count width height bits path unary status) 1 bits' =
      words k context count width height bits' path unary status := by
  apply Function.update_eq_iff.mpr
  refine ⟨rfl, fun i hi => ?_⟩
  have hv : i.val ≠ 1 := fun h => hi (Fin.ext h)
  simp [words, hv]

/-- Replacing tape four changes precisely the unary depth word. -/
theorem words_update_unary (k : ℕ) (context count width height bits path unary unary' : List Bool)
    (status : Bool) :
    Function.update (words k context count width height bits path unary status) 4 unary' =
      words k context count width height bits path unary' status := by
  apply Function.update_eq_iff.mpr
  refine ⟨rfl, fun i hi => ?_⟩
  have hv : i.val ≠ 4 := fun h => hi (Fin.ext h)
  simp [words, hv]

end Turing.MultiTapeATM.CarrySaveLeafLayout
