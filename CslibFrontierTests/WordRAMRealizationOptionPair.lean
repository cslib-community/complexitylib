/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regressions for optional word-pair realization)

public import CslibFrontier.Tactic.Realize

/-!
# Optional extract answers retain both full-word payloads

The default encoding prefixes the existing pair encoding with a presence tag. These clients
exercise both optional branches, maximum payloads and a continuation after a supplied extract
certificate. Native staging remains in the existing realization rules; this adds no decoder
judgment or argument-delivery convention.
-/

public section

namespace Cslib.WordRAM.Realization.Tests.OptionPair

open Cslib.DataStructure

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := WordEncoding.encode
private abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) := WordEncoding.encode
private abbrev optionalWords : Option (ℕ × ℕ) ↪ (Fin 3 → ℕ) := WordEncoding.encode

-- The scalar instance keeps its original definitional encoding.
example : WordEncoding.encode (α := Option ℕ) = optionWords := rfl

example : optionalWords none = ![0, 0, 0] := by
  funext i
  fin_cases i <;> rfl

example (v k : ℕ) : optionalWords (some (v, k)) = ![1, v, k] := by
  funext i
  fin_cases i <;> rfl

example : optionalWords none ≠ optionalWords (some (0, 0)) := by decide
example : ∀ i, Fits 0 (optionalWords none i) := by decide
example : ∀ i, Fits 8 (optionalWords (some (255, 255)) i) := by decide

/-- An extract-style continuation returns both payload words, or two zeros when absent. -/
theorem match_pair_realizes : Realizes .exact
    (fun e : Option (ℕ × ℕ) => match e with
      | none => (pure (0, 0) : Memory.Prog (ℕ × ℕ))
      | some (v, k) => pure (v, k))
    (WordEncoding.encode (α := Option (ℕ × ℕ))) (WordEncoding.encode (α := ℕ × ℕ))
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Existing scalar optional clients keep their two-word encoding and split path.
example : Realizes .exact
    (fun e : Option ℕ => match e with
      | none => (pure 0 : Memory.Prog ℕ)
      | some v => pure v)
    optionWords word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Constructing a present answer explicitly pays its tag fit; neither payload is incremented.
example : Realizes .exact
    (fun p : ℕ × ℕ => (pure (some p) : Memory.Prog (Option (ℕ × ℕ))))
    pairWords optionalWords (fun w _ _ => Fits w 1) (fun _ _ => 0) := by
  realize
  exact h

-- The extract certificate is opaque to this proof. Only its supplied realization is used;
-- the actual result and reached memory feed the checked continuation and bind rule.
example (extract : ℕ → Memory.Prog (Option (ℕ × ℕ)))
    (safe : ℕ → ℕ → Memory.State → Prop) (work : ℕ → Memory.State → ℕ)
    (hExtract : Realizes .exact extract word optionalWords safe work) :
    Realizes .exact (fun d => do
      match ← extract d with
      | none => pure (0, 0)
      | some (v, k) => pure (v, k))
      word pairWords safe (fun d s => work d s + 1) := by
  have hContinue : Realizes .exact
      (fun e : ℕ × Option (ℕ × ℕ) => match e.2 with
        | none => (pure (0, 0) : Memory.Prog (ℕ × ℕ))
        | some (v, k) => pure (v, k))
      (appendWords word optionalWords) pairWords
      (fun _ _ _ => True) (fun _ _ => 0) := by
    realize
  apply (hExtract.bind hContinue).consequence
  · intro w d s _ _ hs
    exact ⟨hs, trivial⟩
  · intro d s
    exact le_rfl

/-- One emitted body handles both branches at different widths and retains both maximal
payload words, while preserving the full initial memory in each execution. -/
theorem same_body_zero_and_max : ∃ r C, ∃ code : Code .exact r, ∃ result : Fin 2 → Fin r,
    ∃ x₀ y₀ x₁ y₁ : Data r,
      x₀.Bounded 0 ∧ x₁.Bounded 8 ∧
      ExecWithin 0 code x₀ y₀ C ∧ (∀ i, y₀.regs (result i) = 0) ∧ y₀.mem = x₀.mem ∧
      ExecWithin 8 code x₁ y₁ C ∧ (∀ i, y₁.regs (result i) = 255) ∧ y₁.mem = x₁.mem := by
  obtain ⟨n, C, emit, he⟩ := match_pair_realizes
  let r := 4 + (2 + n + 1)
  let frontier : Fin r := ⟨0, by omega⟩
  let src : Fin 3 → Fin r := fun i => ⟨1 + i.val, by omega⟩
  let tmp : Fin (2 + n + 1) → Fin r := fun i => ⟨4 + i.val, by omega⟩
  let result : Fin 2 → Fin r := fun i => tmp (Fin.castAdd (n + 1) i)
  have hi : Function.Injective tmp := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp only [tmp] at this
    omega
  have hd (i : Fin 3) (j : Fin (2 + n + 1)) : src i ≠ tmp j := by
    intro h
    have := congrArg Fin.val h
    dsimp only [src, tmp] at this
    have := i.isLt
    omega
  have hf (j : Fin (2 + n + 1)) : tmp j ≠ frontier := by
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
  let x₁ : Data r := ⟨fun i => if i.val = 1 then 1 else
    if i.val = 2 ∨ i.val = 3 then 255 else 0, fun _ => 7⟩
  have hx₀ : x₀.Bounded 0 := ⟨fun _ => fits_zero 0, fun _ => fits_zero 0⟩
  have hx₁ : x₁.Bounded 8 := by
    constructor
    · intro i
      change Fits 8 (if i.val = 1 then 1 else if i.val = 2 ∨ i.val = 3 then 255 else 0)
      split_ifs <;> decide
    · intro a
      change Fits 8 7
      decide
  have hin₀ : x₀.regs ∘ src = optionalWords none := by
    funext i
    fin_cases i <;> rfl
  have hin₁ : x₁.regs ∘ src = optionalWords (some (255, 255)) := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨_, hrun⟩ := he frontier src tmp hi hd hf hs
  obtain ⟨y₀, hy₀, hm₀, ho₀, _⟩ := hrun 0 none x₀ hx₀ hin₀ trivial (by trivial)
  obtain ⟨y₁, hy₁, hm₁, ho₁, _⟩ := hrun 8 (some (255, 255)) x₁ hx₁ hin₁ trivial (by trivial)
  have hy₀' : ExecWithin 0 (emit frontier src tmp) x₀ y₀ C := by
    simpa only [memoryCost_pure, Nat.zero_add, Nat.add_zero, Nat.mul_one] using hy₀
  have hy₁' : ExecWithin 8 (emit frontier src tmp) x₁ y₁ C := by
    simpa only [memoryCost_pure, Nat.zero_add, Nat.add_zero, Nat.mul_one] using hy₁
  refine ⟨r, C, emit frontier src tmp, result, x₀, y₀, x₁, y₁, hx₀, hx₁, hy₀', ?_,
    congrArg Memory.State.mem hm₀, hy₁', ?_, congrArg Memory.State.mem hm₁⟩
  · intro i
    have h := ho₀ i
    change y₀.regs (result i) = _ at h
    fin_cases i <;> exact h
  · intro i
    have h := ho₁ i
    change y₁.regs (result i) = _ at h
    fin_cases i <;> exact h

/--
error: realize: optional matches support a word or a pair of words, got
  Option Bool
-/
#guard_msgs in
example : Realizes .exact
    (fun e : Option Bool => match e with
      | none => (pure 0 : Memory.Prog ℕ)
      | some b => pure (if b then 1 else 0))
    (WordEncoding.encode (α := Option Bool)) word
    (fun w _ _ => Fits w 1) (fun _ _ => 0) := by
  realize

end Cslib.WordRAM.Realization.Tests.OptionPair
