/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression clients for uniform product dispatch)

public import Complexity.Computability.WordRAM.Realization.Product
public import Complexity.Computability.WordRAM.Realization.Glue

/-!
# One dispatcher at two widths

The same native emitter copies the left input and returns zero on the right. Its source issues
no memory operations, but both the local word operation and the dispatch remain charged. The
left zero input runs at width zero; the right tag naturally requires a positive width. The
conditional compares the tag register with the encoded zero register, not a literal register
index standing for zero.
-/

public section

namespace Cslib.WordRAM.Realization.Tests.Product

open Cslib.DataStructure

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

private def environment : ℕ ⊕ ℕ ↪ (Fin 3 → ℕ) where
  toFun := Sum.elim (fun a => ![0, a, 0]) (fun b => ![1, b, 0])
  inj' := by
    intro a b h
    cases a <;> cases b
    · exact congrArg Sum.inl (congrFun h 1)
    · have := congrFun h 0
      simp at this
    · have := congrFun h 0
      simp at this
    · exact congrArg Sum.inr (congrFun h 1)

private theorem copy_realizes :
    Realizes .exact (fun d : ℕ => (pure d : Memory.Prog ℕ)) word word
      (fun _ _ _ => True) (fun _ _ => 1) := by
  apply (Realizes.glue word (GlueComputes.proj (B := .exact)
    (P := fun _ : Fin 1 → ℕ => True) (bound := fun v => v 0) 0
    (fun _ _ => le_rfl))).consequence
  · intro w d s hwords _ _
    exact ⟨trivial, hwords 0⟩
  · intro d s
    exact le_rfl

private theorem zero_realizes :
    Realizes .exact (fun _ : ℕ => (pure 0 : Memory.Prog ℕ)) word word
      (fun _ _ _ => True) (fun _ _ => 1) := by
  apply (Realizes.glue word (GlueComputes.const (B := .exact)
    (P := fun _ : Fin 1 → ℕ => True) (bound := fun _ => 0) 0
    (fun _ _ => le_rfl))).consequence
  · intro w d s _ _ _
    exact ⟨trivial, fits_zero w⟩
  · intro d s
    exact le_rfl

private theorem dispatch_realizes :
    Realizes .exact
      (Sum.elim (fun a : ℕ => (pure a : Memory.Prog ℕ)) (fun _ : ℕ => pure 0))
      environment word (fun _ _ _ => True) (fun _ _ => 3) := by
  have h := copy_realizes.sum zero_realizes environment (fun _ => 1) (fun _ => 1)
    (by intro d i; fin_cases i; rfl) (by intro d i; fin_cases i; rfl)
    (.eq 0 2) (by intro d; rfl) (by intro d; change ¬(1 = 0); decide)
  apply h.consequence
  · intro w d s _ _ _
    cases d <;> trivial
  · intro d s
    cases d <;> exact le_rfl

/-- A single emitted code runs at width zero on the left and width four on the right. The
inaccessible memory is preserved literally. At width four the two summands receive the same
payload but return different answers, ruling out a constant-output witness. -/
theorem same_code_two_widths : ∃ r C, ∃ code : Code .exact r, ∃ result : Fin r,
    ∃ x₀ y₀ x₁ y₁ x₂ y₂ : Data r,
      x₀.Bounded 0 ∧ x₁.Bounded 4 ∧
      ExecWithin 0 code x₀ y₀ (C * 4) ∧ y₀.regs result = 0 ∧ y₀.mem = x₀.mem ∧
      ExecWithin 4 code x₁ y₁ (C * 4) ∧ y₁.regs result = 0 ∧ y₁.mem = x₁.mem ∧
      ExecWithin 4 code x₂ y₂ (C * 4) ∧ y₂.regs result = 15 ∧ y₂.mem = x₂.mem ∧
      x₁.mem 100 = 7 ∧ ¬code.ReadsWidth := by
  obtain ⟨n, C, emit, he⟩ := dispatch_realizes
  let r := 4 + (1 + n + 1)
  let frontier : Fin r := ⟨0, by omega⟩
  let src : Fin 3 → Fin r := fun i => ⟨1 + i.val, by omega⟩
  let tmp : Fin (1 + n + 1) → Fin r := fun i => ⟨4 + i.val, by omega⟩
  have hi : Function.Injective tmp := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp only [tmp] at this
    omega
  have hd (i : Fin 3) (j : Fin (1 + n + 1)) : src i ≠ tmp j := by
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
  have hs (i : Fin 3) : src i ≠ frontier := by
    intro h
    have := congrArg Fin.val h
    dsimp only [src, frontier] at this
    omega
  let x₀ : Data r := ⟨fun _ => 0, fun _ => 0⟩
  let x₁ : Data r := ⟨fun i => if i = src 0 then 1 else if i = src 1 then 15 else 0,
    fun _ => 7⟩
  let x₂ : Data r := ⟨fun i => if i = src 1 then 15 else 0, fun _ => 3⟩
  have hx₀ : x₀.Bounded 0 := ⟨fun _ => fits_zero 0, fun _ => fits_zero 0⟩
  have hx₁ : x₁.Bounded 4 := by
    constructor
    · intro i
      change Fits 4 (if i = src 0 then 1 else if i = src 1 then 15 else 0)
      split_ifs <;> decide
    · intro a
      change Fits 4 7
      decide
  have hx₂ : x₂.Bounded 4 := by
    constructor
    · intro i
      change Fits 4 (if i = src 1 then 15 else 0)
      split_ifs <;> decide
    · intro a
      change Fits 4 3
      decide
  have hin₀ : x₀.regs ∘ src = environment (.inl 0) := by
    funext i
    fin_cases i <;> rfl
  have hin₁ : x₁.regs ∘ src = environment (.inr 15) := by
    funext i
    fin_cases i <;> rfl
  have hin₂ : x₂.regs ∘ src = environment (.inl 15) := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  obtain ⟨y₀, hy₀, hm₀, ho₀, _⟩ := hrun 0 (.inl 0) x₀ hx₀ hin₀ trivial (by trivial)
  obtain ⟨y₁, hy₁, hm₁, ho₁, _⟩ := hrun 4 (.inr 15) x₁ hx₁ hin₁ trivial (by trivial)
  obtain ⟨y₂, hy₂, hm₂, ho₂, _⟩ := hrun 4 (.inl 15) x₂ hx₂ hin₂ trivial (by trivial)
  refine ⟨r, C, emit frontier src tmp, tmp 0, x₀, y₀, x₁, y₁, x₂, y₂, hx₀, hx₁,
    hy₀, ho₀ 0, congrArg Memory.State.mem hm₀,
    hy₁, ho₁ 0, congrArg Memory.State.mem hm₁,
    hy₂, ho₂ 0, congrArg Memory.State.mem hm₂, rfl, hnw⟩

-- The left encoded environment fits at width zero, whereas the right tag cannot.
example : ∀ i, Fits 0 (environment (.inl 0) i) := by decide
example : ¬ Fits 0 (environment (.inr 0) 0) := by decide
example : test (.eq 0 2) (environment (.inl 15)) := by decide
example : ¬test (.eq 0 2) (environment (.inr 15)) := by decide

end Cslib.WordRAM.Realization.Tests.Product
