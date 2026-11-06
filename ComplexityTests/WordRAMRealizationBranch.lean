/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of realization branching)

public import Complexity.Computability.WordRAM.Realization.Branch
public import Complexity.Computability.WordRAM.Realization.Glue

/-! The branch that needs `1` is taken only when an input word is positive. Thus the same fixed
program also works at width zero on two zero inputs, without requiring `Fits 0 1`. -/

public section

open Cslib.WordRAM Cslib.WordRAM.Realization

namespace WordRAMRealizationBranchTests

@[expose] def input : (Fin 2 → ℕ) ↪ (Fin 2 → ℕ) := Function.Embedding.refl _

@[expose] def output : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

theorem branch_fits_on_selected_path : Realizes .exact
    (fun v => if v 0 < v 1 then pure 1 else pure 0) input output
    (fun _ _ _ => True) (fun _ _ => 3) := by
  have hp := Realizes.glue input
    (GlueComputes.const (B := .exact) (P := fun _ : Fin 2 → ℕ => True)
      (bound := fun _ => 1) 1 (fun _ _ => le_rfl))
  have hn := Realizes.glue input
    (GlueComputes.const (B := .exact) (P := fun _ : Fin 2 → ℕ => True)
      (bound := fun _ => 0) 0 (fun _ _ => le_rfl))
  have h := Realizes.branch (.lt 0 1) hp hn
  apply h.consequence
  · intro w d s hwords hmem hs
    by_cases hd : d 0 < d 1
    · simp only [test, Cond.Holds, input, Function.Embedding.refl_apply,
        ite_eq_left hd]
      exact ⟨trivial, (hwords 1).of_le (by change 1 ≤ d 1; omega)⟩
    · simp only [test, Cond.Holds, input, Function.Embedding.refl_apply,
        ite_eq_right hd]
      exact ⟨trivial, fits_zero w⟩
  · intro d s
    split <;> exact le_rfl

example : ¬ Fits 0 1 := by decide

example : ¬ test (.lt 0 1) (fun _ : Fin 2 => 0) := by decide

end WordRAMRealizationBranchTests
