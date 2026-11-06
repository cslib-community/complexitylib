/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression clients for finite-result glue realization)

public import Complexity.Computability.WordRAM.Realization.GlueVector

/-!
# Optional-word vector glue regressions

Every coordinate is computed by an actual scalar certificate. `none` uses two zero constants
and remains valid at word width zero; `some v` uses a presence constant and an unshifted word
projection, including the maximal word. Empty results retain the charged neutral-copy case.
-/

public section

namespace Cslib.WordRAM.Realization.Tests

open Cslib.DataStructure

private def unitWords : Unit ↪ (Fin 0 → ℕ) :=
  (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding

private def wordInput : ℕ ↪ (Fin 1 → ℕ) :=
  (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

private theorem none_realizes :
    Realizes .exact (fun _ : Unit => pure (none : Option ℕ)) unitWords optionWords
      (fun w _ _ => True ∧ ∀ _ : Fin 2, Fits w 0) (fun _ _ => 4) := by
  have hcoord (i : Fin 2) : GlueComputes .exact (fun _ : Fin 0 → ℕ => True)
      (fun _ => 0) (fun _ => 0) 1 := GlueComputes.const 0 (fun _ _ => le_rfl)
  have hresult (d : Unit) (i : Fin 2) : optionWords none i = 0 := by
    fin_cases i <;> rfl
  simpa using Realizes.glueVector unitWords optionWords (fun _ => none)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ => 1) hresult hcoord

private def someCoordinate : Fin 2 → (Fin 1 → ℕ) → ℕ := ![fun _ => 1, fun v => v 0]

private theorem some_realizes :
    Realizes .exact (fun v : ℕ => pure (some v)) wordInput optionWords
      (fun w v _ => True ∧ Fits w 1 ∧ Fits w v) (fun _ _ => 4) := by
  have hcoord (i : Fin 2) : GlueComputes .exact (fun _ : Fin 1 → ℕ => True)
      (someCoordinate i) (someCoordinate i) 1 := by
    fin_cases i
    · exact GlueComputes.const 1 (fun _ _ => le_rfl)
    · exact GlueComputes.proj 0 (fun _ _ => le_rfl)
  have hresult (v : ℕ) (i : Fin 2) : optionWords (some v) i =
      someCoordinate i (wordInput v) := by
    fin_cases i <;> rfl
  simpa [someCoordinate, wordInput, Fin.forall_fin_succ] using
    Realizes.glueVector wordInput optionWords some someCoordinate someCoordinate
      (fun _ => 1) hresult hcoord

private theorem unit_realizes :
    Realizes .exact (fun _ : Unit => pure ()) unitWords unitWords
      (fun _ _ _ => True ∧ True) (fun _ _ => 0) := by
  have hcoord (i : Fin 0) : GlueComputes .exact (fun _ : Fin 0 → ℕ => True)
      (Fin.elim0 i) (Fin.elim0 i) (Fin.elim0 i) := Fin.elim0 i
  have hresult (d : Unit) (i : Fin 0) :
      unitWords () i = (Fin.elim0 i : (Fin 0 → ℕ) → ℕ) (unitWords d) :=
    Fin.elim0 i
  simpa using Realizes.glueVector unitWords unitWords (fun _ => ())
    Fin.elim0 Fin.elim0 Fin.elim0 hresult hcoord

/-- The optional payload is not shifted, so the maximal two-bit word is retained. -/
theorem optionWords_some_max : optionWords (some 3) = ![1, 3] := rfl

example : optionWords none ≠ optionWords (some 0) := by decide
example : ¬Fits 0 (optionWords (some 0) 0) := by decide
example : Fits 2 (optionWords (some 3) 0) ∧ Fits 2 (optionWords (some 3) 1) := by decide

/-- The certified two-coordinate `none` emitter actually executes at width zero. -/
example : ∃ r, ∃ p : Program .exact r, ∃ steps,
    Executes 0 p ⟨0, ⟨fun _ => 0, fun _ => 0⟩⟩ 0 steps := by
  obtain ⟨n, C, emit, he⟩ := none_realizes
  let r := (2 + n + 1) + 1
  let frontier : Fin r := ⟨r - 1, by omega⟩
  let src : Fin 0 → Fin r := Fin.elim0
  let tmp : Fin (2 + n + 1) → Fin r := fun i => ⟨i.val, by omega⟩
  have hi : Function.Injective tmp := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun i : Fin r => i.val) h
  have hf (j : Fin (2 + n + 1)) : tmp j ≠ frontier := by
    intro h
    have hh := congrArg (fun i : Fin r => i.val) h
    dsimp only [tmp, frontier, r] at hh
    omega
  let x : Data r := ⟨fun _ => 0, fun _ => 0⟩
  have hx : x.Bounded 0 := ⟨fun _ => fits_zero 0, fun _ => fits_zero 0⟩
  have hin : x.regs ∘ src = unitWords () := Subsingleton.elim _ _
  obtain ⟨y, ⟨steps, _, hy⟩, _, hout, _⟩ :=
    (he frontier src tmp hi (fun i => Fin.elim0 i) hf (fun i => Fin.elim0 i)).2
      0 () x hx hin ⟨trivial, fun _ => fits_zero 0⟩ trivial
  have ho : y.regs (tmp 0) = 0 := hout 0
  refine ⟨r, (emit frontier src tmp).program (tmp 0), steps + 1, ?_⟩
  simpa only [ho] using hy.executes (tmp 0)

example : boolWords false = ![0, 0] := rfl
example : Fits 0 (boolWords false 0) ∧ Fits 0 (boolWords false 1) := by decide
example : ¬Fits 0 (boolWords true 0) := by decide

/-- The certified payload emitter returns the maximal two-bit word without incrementing it. -/
example : ∃ r, ∃ p : Program .exact r, ∃ x : Data r, ∃ steps,
    x.Bounded 2 ∧ Executes 2 p ⟨0, x⟩ 3 steps := by
  obtain ⟨n, C, emit, he⟩ := some_realizes
  let r := 1 + (2 + n + 1) + 1
  let frontier : Fin r := ⟨r - 1, by omega⟩
  let src : Fin 1 → Fin r := fun i => ⟨i.val, by omega⟩
  let tmp : Fin (2 + n + 1) → Fin r := fun i => ⟨1 + i.val, by omega⟩
  have hi : Function.Injective tmp := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun i : Fin r => i.val) h
    dsimp only [tmp] at hh
    omega
  have hd (i : Fin 1) (j : Fin (2 + n + 1)) : src i ≠ tmp j := by
    intro h
    have hh := congrArg (fun i : Fin r => i.val) h
    dsimp only [src, tmp] at hh
    omega
  have hf (j : Fin (2 + n + 1)) : tmp j ≠ frontier := by
    intro h
    have hh := congrArg (fun i : Fin r => i.val) h
    dsimp only [tmp, frontier, r] at hh
    omega
  have hs (i : Fin 1) : src i ≠ frontier := by
    intro h
    have hh := congrArg (fun i : Fin r => i.val) h
    dsimp only [src, frontier, r] at hh
    omega
  let x : Data r := ⟨fun i => if i = src 0 then 3 else 0, fun _ => 0⟩
  have hx : x.Bounded 2 := by
    refine ⟨fun i => ?_, fun _ => fits_zero 2⟩
    change Fits 2 (if i = src 0 then 3 else 0)
    split_ifs <;> decide
  have hin : x.regs ∘ src = wordInput 3 := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [x, wordInput]
  obtain ⟨y, ⟨steps, _, hy⟩, _, hout, _⟩ :=
    (he frontier src tmp hi hd hf hs).2 2 3 x hx hin ⟨trivial, by decide, by decide⟩ trivial
  let out := tmp (Fin.castAdd (n + 1) (1 : Fin 2))
  have ho : y.regs out = 3 := hout 1
  refine ⟨r, (emit frontier src tmp).program out, x, steps + 1, hx, ?_⟩
  simpa only [ho] using hy.executes out

end Cslib.WordRAM.Realization.Tests
