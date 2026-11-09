/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (captured iterate environment regression tests)

public import CslibFrontier.Tactic.Realize

/-!
# Iteration steps retain runtime captures

The explicit loop environment can be `Unit` while the step closes over other live runtime words.
The same source, input encoding, per-step memory query and zero local-work grading are retained.
-/

public section

namespace Cslib.WordRAM.Realization.Tests.IterateCapture

open Cslib.DataStructure

/-- The read address is captured; neither the initial state nor the count selects native code. -/
theorem captured_read : Realizes .exact
    (fun d : Fin 3 → ℕ => iterate (fun _ : Unit × ℕ => Memory.read (d 0)) () (d 1) (d 2))
    (.refl _) (WordEncoding.encode (α := ℕ)) (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Captures are also adapted when the explicit loop argument is the whole environment. -/
theorem captured_read_whole : Realizes .exact
    (fun d : Fin 3 → ℕ =>
      iterate (fun _ : (Fin 3 → ℕ) × ℕ => Memory.read (d 0)) d (d 1) (d 2))
    (.refl _) (WordEncoding.encode (α := ℕ)) (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- A separately certified call keeps its domain at every reached memory, in the original
captured source's terms rather than an auxiliary environment chosen by the frontend. -/
theorem captured_call (m : ℕ × ℕ → Memory.Prog ℕ)
    (P : ℕ → ℕ × ℕ → Memory.State → Prop)
    (hm : Realizes .exact m (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ)) P (fun _ _ => 0)) :
    Realizes .exact
      (fun d : Fin 3 → ℕ => iterate (fun _ : Unit × ℕ => do
        let v ← Memory.read (d 0)
        m (d 0, v)) () (d 1) (d 2))
      (.refl _) (WordEncoding.encode (α := ℕ))
      (fun w d s => iterationSafe
        (fun _ : Unit × ℕ => do let v ← Memory.read (d 0); m (d 0, v))
        (fun w _ s => P w (d 0, s.mem (d 0)) s) w () (d 1) (d 2) s)
      (fun _ _ => 0) := by
  realize
  exact h

/-- The same emitted body handles distinct captured addresses and zero/two iterations.
Both executions retain every initial memory cell; the query count remains charged. -/
theorem same_body_distinct_environments : ∃ r C, ∃ code : Code .exact r,
    ∃ result : Fin r, ∃ x₀ y₀ x₁ y₁ : Data r,
      ¬code.ReadsWidth ∧ x₀.Bounded 3 ∧ x₁.Bounded 3 ∧
      ExecWithin 3 code x₀ y₀ C ∧ y₀.regs result = 5 ∧ y₀.mem = x₀.mem ∧
      ExecWithin 3 code x₁ y₁ (3 * C) ∧ y₁.regs result = 7 ∧ y₁.mem = x₁.mem := by
  obtain ⟨n, C, emit, he⟩ := captured_read
  let r := 4 + (1 + n + 1)
  let frontier : Fin r := ⟨0, by omega⟩
  let src : Fin 3 → Fin r := fun i => ⟨1 + i.val, by omega⟩
  let tmp : Fin (1 + n + 1) → Fin r := fun i => ⟨4 + i.val, by omega⟩
  let result := tmp 0
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
  let d₀ : Fin 3 → ℕ := ![1, 0, 5]
  let d₁ : Fin 3 → ℕ := ![2, 2, 0]
  let x₀ : Data r := ⟨fun i => if i.val = 0 then 3 else
    if i.val = 1 then 1 else if i.val = 3 then 5 else 0, fun _ => 7⟩
  let x₁ : Data r := ⟨fun i => if i.val = 0 then 3 else
    if i.val = 1 ∨ i.val = 2 then 2 else 0, fun _ => 7⟩
  have hx₀ : x₀.Bounded 3 := by
    constructor
    · intro i
      change Fits 3 (if i.val = 0 then 3 else
        if i.val = 1 then 1 else if i.val = 3 then 5 else 0)
      split_ifs <;> decide
    · intro a
      change Fits 3 7
      decide
  have hx₁ : x₁.Bounded 3 := by
    constructor
    · intro i
      change Fits 3 (if i.val = 0 then 3 else if i.val = 1 ∨ i.val = 2 then 2 else 0)
      split_ifs <;> decide
    · intro a
      change Fits 3 7
      decide
  have hin₀ : x₀.regs ∘ src = d₀ := by funext i; fin_cases i <;> rfl
  have hin₁ : x₁.regs ∘ src = d₁ := by funext i; fin_cases i <;> rfl
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  obtain ⟨y₀, hy₀, hm₀, ho₀, _⟩ := hrun 3 d₀ x₀ hx₀ hin₀ trivial (by trivial)
  obtain ⟨y₁, hy₁, hm₁, ho₁, _⟩ := hrun 3 d₁ x₁ hx₁ hin₁ trivial (by
    change 2 < 3 ∧ 2 < 3 ∧ True
    decide)
  have hc₀ : memoryCost (iterate (fun _ : Unit × ℕ => Memory.read (d₀ 0)) () (d₀ 1)
      (d₀ 2)) (memoryState frontier x₀) = 0 := rfl
  have hc₁ : memoryCost (iterate (fun _ : Unit × ℕ => Memory.read (d₁ 0)) () (d₁ 1)
      (d₁ 2)) (memoryState frontier x₁) = 2 := rfl
  have hy₀' : ExecWithin 3 (emit frontier src tmp) x₀ y₀ C := by
    simpa only [hc₀, Nat.zero_add, Nat.add_zero, Nat.mul_one]
      using hy₀
  have hy₁' : ExecWithin 3 (emit frontier src tmp) x₁ y₁ (3 * C) := by
    simpa only [hc₁, Nat.add_zero, Nat.reduceAdd, Nat.mul_comm]
      using hy₁
  exact ⟨r, C, emit frontier src tmp, result, x₀, y₀, x₁, y₁, hnw, hx₀, hx₁, hy₀',
    ho₀ 0, congrArg Memory.State.mem hm₀, hy₁', ho₁ 0, congrArg Memory.State.mem hm₁⟩

end Cslib.WordRAM.Realization.Tests.IterateCapture
